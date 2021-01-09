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
)

// QuantifierChecker encapsulates all functionality needed to deal with quantifiers as part of the specification.
type QuantifierChecker struct {
	tokenFile *token.File
	pkg       *types.Package
	astFile   *ast.File
	racInfos  *[]RACInfo
}

// NewQuantifierChecker creates and returns a new QuantifierChecker object.
func NewQuantifierChecker(tokenFile *token.File, pkg *types.Package, astFile *ast.File, racInfos *[]RACInfo) (qc *QuantifierChecker) {
	return &QuantifierChecker{
		tokenFile: tokenFile,
		pkg:       pkg,
		astFile:   astFile,
		racInfos:  racInfos,
	}
}

// check iterates through all racInfo objects and check whether all variables used in quantifiers (except boolean ones)
// are bounded.
func (qc QuantifierChecker) check() {
	for _, racInfo := range *qc.racInfos {
		quantifiers := racInfo.DesugaredNode().extractQuantifiers()
		if ok, unboundedVar, quantifier := qc.checkQuantifiers(quantifiers); !ok {
			panic(fmt.Sprintf("Quantifier '%v' from specification '%v' at line %d needs bound for variable '%s'",
				quantifier, racInfo, qc.tokenFile.Line(racInfo.Pos()), unboundedVar))
		}
	}
}

// checkQuantifiers checks for each quantifier in a given list of quantifiers whether all the quantified variables
// that are not boolean are bounded.
func (qc QuantifierChecker) checkQuantifiers(quantifiers []Quantifier) (bool, string, Quantifier) {
	for _, quantifier := range quantifiers {
		if ok, unboundedVar := qc.checkVariableBounds(quantifier.QuantifiedVars(), quantifier.Domain()); !ok {
			return false, unboundedVar, quantifier
		}
	}
	return true, "", nil
}

// checkVariableBounds checks for a given list of quantified variables, whether the belonging domain has at least one
// constraint for it. An exception is made for boolean quantified variables since they can only have two values and
// thus do not need to be bounded.
func (qc QuantifierChecker) checkVariableBounds(quantifiedVars []Identifier, domain *Domain) (bool, string) {
	if domain == nil {
		for _, quantifiedVar := range quantifiedVars {
			if !(quantifiedVar.type_ == types.Typ[types.UntypedBool] || quantifiedVar.type_ == types.Typ[types.Bool]) {
				return false, quantifiedVar.String()
			}
		}
	} else {
		boundedVars := map[string]*Identifier{}
		domain.extractBoundedVars(&boundedVars)
		for _, quantifiedVar := range quantifiedVars {
			if !(quantifiedVar.type_ == types.Typ[types.UntypedBool] || quantifiedVar.type_ == types.Typ[types.Bool]) {
				if _, ok := boundedVars[quantifiedVar.String()]; !ok {
					return false, quantifiedVar.String()
				}
			}
		}
	}
	return true, ""
}
