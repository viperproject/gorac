// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/ast/astutil"
	"log"
)

type Placement struct {
	node         ast.Node
	insertBefore bool
}

// OldExprConverter encapsulates all functionality needed to deal with old expressions as part of the specification.
type OldExprConverter struct {
	tokenFile        *token.File
	pkg              *types.Package
	astFile          *ast.File
	specInfos        *[]SpecInfo
	racInfos         *[]RACInfo
	labelMap         *map[string]Placement
	racOldMap        *map[RACInfo][]Old
	sharedVarsMap    *map[string]*types.Scope
	exclusiveVarsMap *map[string]*types.Scope
}

// NewOldExprConverter creates and returns a new OldExprConverter object.
func NewOldExprConverter(tokenFile *token.File, pkg *types.Package, astFile *ast.File, specInfos *[]SpecInfo,
	racInfos *[]RACInfo, sharedVarsMap, exclusiveVarsMap *map[string]*types.Scope) (o *OldExprConverter) {
	labelMap := make(map[string]Placement)
	racOldMap := make(map[RACInfo][]Old)
	oldExprConverter := &OldExprConverter{
		tokenFile:        tokenFile,
		pkg:              pkg,
		astFile:          astFile,
		specInfos:        specInfos,
		racInfos:         racInfos,
		labelMap:         &labelMap,
		racOldMap:        &racOldMap,
		sharedVarsMap:    sharedVarsMap,
		exclusiveVarsMap: exclusiveVarsMap,
	}
	oldExprConverter.fillLabelMap()
	oldExprConverter.fillRacOldMap()
	return oldExprConverter
}

// fillLabelMap fills the labelMap such that each old expression is mapped to the label where its declaration should
// be inserted.
func (o *OldExprConverter) fillLabelMap() {
	o.extractSpecLabels()
	o.extractGoLabels()
}

// extractSpecLabels extracts all specification labels from the list of SpecInfo objects and saves them in the labelMap.
func (o *OldExprConverter) extractSpecLabels() {
	for _, specInfo := range *o.specInfos {
		if label, ok := specInfo.(*LabelInfo); ok {
			o.addToLabelMap(label.name, label.pos, label.associatedNode, label.insertBefore)
		}
	}
}

// extractGoLabels extracts all Go labels of the program and saves them in the labelMap.
func (o *OldExprConverter) extractGoLabels() {
	astutil.Apply(o.astFile, func(c *astutil.Cursor) bool {
		switch c.Node().(type) {
		case *ast.LabeledStmt:
			label := c.Node().(*ast.LabeledStmt)
			o.addToLabelMap(label.Label.Name, label.Pos(), label, true)
		}
		return true
	}, nil)
}

// addToLabelMap adds a label name, the node where the corresponding label is attached to and the position
// (before or after) to the labelMap.
func (o *OldExprConverter) addToLabelMap(name string, pos token.Pos, node ast.Node, insertBefore bool) {
	if placement, ok := (*o.labelMap)[name]; ok {
		panic(fmt.Sprintf("Label %s defined twice at line %v and line %v",
			name, o.tokenFile.Line(pos), o.tokenFile.Line(placement.node.Pos())))
	}
	(*o.labelMap)[name] = Placement{
		node:         node,
		insertBefore: insertBefore,
	}
}

// fillRacOldMap goes through all RACInfo objects and extracts all old expressions used. Since no old expressions are
// allowed to be used in preconditions, a special check for this is called. For all other nodes, the set of old
// expressions are saved in the racOldMap of the OldExprConverter.
func (o *OldExprConverter) fillRacOldMap() {
	for _, racInfo := range *o.racInfos {
		switch racInfo.(type) {
		case *AssertInfo, *PostCondInfo, *InvariantInfo:
			(*o.racOldMap)[racInfo] = racInfo.DesugaredNode().extractOldExpressions(o.labelMap, racInfo, o.tokenFile)
		case *PreCondInfo:
			o.checkPreCond(racInfo.(*PreCondInfo))
		}
	}
}

// checkPreCond checks whether no old expressions are used in the given precondition. If there are, a panic occurs.
func (o *OldExprConverter) checkPreCond(pre *PreCondInfo) {
	if len(pre.DesugaredNode().extractOldExpressions(o.labelMap, pre, o.tokenFile)) > 0 {
		panic(fmt.Sprintf("No old expressions allowed in precondition %v at line %v.",
			pre, o.tokenFile.Line(pre.Pos())))
	}
}

// addAssignments adds for all RACInfo objects that are allowed to contain old expressions assignments of these old
// expressions to the correct place in the Go AST. Only postconditions are allowed to contain exclusive variables since
// they will be treated like shared ones.
func (o *OldExprConverter) addAssignments() {
	for _, racInfo := range *o.racInfos {
		switch racInfo.(type) {
		case *AssertInfo:
			o.addAssignmentsForSpecInfo(racInfo, racInfo.(*AssertInfo).parentFunction, false)
		case *PostCondInfo:
			o.addAssignmentsForSpecInfo(racInfo, (*racInfo.AssociatedNode()).(*ast.FuncDecl), true)
		case *InvariantInfo:
			o.addAssignmentsForSpecInfo(racInfo, racInfo.(*InvariantInfo).parentFunction, false)
		}
	}
}

// addAssignmentsForSpecInfo adds the identifier assignments of each old expression to the Go AST. For unlabelled old
// expressions, the assignment is added at the beginning of the function. For labelled old expressions, the values are
// assigned after the labels. Declarations of the identifiers are added later using addDeclarations().
func (o *OldExprConverter) addAssignmentsForSpecInfo(racInfo RACInfo, parentFunction *ast.FuncDecl, exclusiveAllowed bool) {
	for _, old := range (*o.racOldMap)[racInfo] {
		o.checkExclusiveVars(old, exclusiveAllowed, racInfo, parentFunction.Pos())
		decl := assignStmt([]ast.Expr{old.identifier.toRAC().(ast.Expr)},
			[]ast.Expr{old.expression.toRAC().(ast.Expr)}, token.ASSIGN)
		if old.label == "" {
			// For unlabelled old expressions, the assignment of the old expression variable is added at the beginning
			// of the function
			insertIntoFunctionBody(parentFunction, decl)
		} else {
			// For labelled old expressions, the assignment of the old expression variable is added right after the label
			placement := (*o.labelMap)[old.label]
			insert(o.astFile, placement.node, decl, placement.insertBefore)
		}
	}
}

// checkExclusiveVars checks for a given old expression whether no exclusive variable is used in positions where we do
// not support the runtime check generation for exclusive old. For this, all identifiers are extracted from the old
// expression. For each identifier it is checked whether it is
// (1) declared as shared
// (2) declared as exclusive
// (3) not declared at all and therefore considered exclusive by default
// In case (1) the runtime check can be generated since all shared variables are supported, therefore, we continue with
// the next identifier. In case (2) is it checked whether exclusive variables are allowed which is only the case for
// postconditions. If they are not allowed, a panic is thrown. Otherwise, the scope is checked as for shared variables.
// In the last case (3) it is checked as for (2) whether exclusive variables are allowed.
func (o *OldExprConverter) checkExclusiveVars(old Old, exclusiveAllowed bool, racInfo RACInfo, pos token.Pos) {
	for _, identifier := range old.extractIdentifiers() {
		if scope := (*o.sharedVarsMap)[identifier.value]; scope != nil {
			continue
		} else if scope := (*o.exclusiveVarsMap)[identifier.value]; scope != nil {
			if !exclusiveAllowed {
				panic(fmt.Sprintf("At line %d in old expression '%v' the exclusive variable '%v' is not allowed. "+
					"Exclusive variables are supported in postconditions only. Declare '%v' as shared or remove from old expression.",
					o.tokenFile.Line(racInfo.Pos()), old, identifier, identifier))
			}
		} else {
			// Neither declared as shared nor as exclusive, therefore considered by default as exclusive
			if !exclusiveAllowed {
				panic(fmt.Sprintf("At line %d in old expression '%v' the variable '%v' is considered by default as exclusive. "+
					"However, exclusive variables are supported in postconditions only. Declare '%v' as shared or remove from old expression.",
					o.tokenFile.Line(racInfo.Pos()), old, identifier, identifier))
			}
			log.Printf("At line %d in old expression '%v' variable '%v' is considered exclusive.",
				o.tokenFile.Line(racInfo.Pos()), old, identifier)
		}
	}
}

// addDeclarations adds for all RACInfo objects that are allowed to contain old expressions declarations of these old
// expressions to the Go AST.
func (o *OldExprConverter) addDeclarations() {
	for _, racInfo := range *o.racInfos {
		switch racInfo.(type) {
		case *AssertInfo:
			o.addDeclarationsForSpecInfo(racInfo, racInfo.(*AssertInfo).parentFunction)
		case *PostCondInfo:
			o.addDeclarationsForSpecInfo(racInfo, (*racInfo.AssociatedNode()).(*ast.FuncDecl))
		case *InvariantInfo:
			o.addDeclarationsForSpecInfo(racInfo, racInfo.(*InvariantInfo).parentFunction)
		}
	}
}

// addDeclarationsForSpecInfo adds declarations for all of the old expressions used in the given SpecInfo object to the
// beginning of the function the specification is a part of.
func (o *OldExprConverter) addDeclarationsForSpecInfo(racInfo RACInfo, parentFunction *ast.FuncDecl) {
	for _, old := range (*o.racOldMap)[racInfo] {
		typeIdentifier := getTypeIdentifier(old.Type())
		decl := declStmt(genDecl(token.VAR,
			[]ast.Spec{valueSpec([]*ast.Ident{ident(old.identifier.value)}, ident(typeIdentifier))}))
		insertIntoFunctionBody(parentFunction, decl)
	}
}
