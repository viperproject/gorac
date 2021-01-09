// Code generated from SpecGrammar.g4 by ANTLR 4.7.1. DO NOT EDIT.

package specparser // SpecGrammar
import (
	"fmt"
	"reflect"
	"strconv"

	"github.com/antlr/antlr4/runtime/Go/antlr"
)

// Suppress unused import errors
var _ = fmt.Printf
var _ = reflect.Copy
var _ = strconv.Itoa

var parserATN = []uint16{
	3, 24715, 42794, 33075, 47597, 16764, 15335, 30598, 22884, 3, 49, 477,
	4, 2, 9, 2, 4, 3, 9, 3, 4, 4, 9, 4, 4, 5, 9, 5, 4, 6, 9, 6, 4, 7, 9, 7,
	4, 8, 9, 8, 4, 9, 9, 9, 4, 10, 9, 10, 4, 11, 9, 11, 4, 12, 9, 12, 4, 13,
	9, 13, 4, 14, 9, 14, 4, 15, 9, 15, 4, 16, 9, 16, 4, 17, 9, 17, 4, 18, 9,
	18, 4, 19, 9, 19, 4, 20, 9, 20, 4, 21, 9, 21, 4, 22, 9, 22, 4, 23, 9, 23,
	4, 24, 9, 24, 4, 25, 9, 25, 4, 26, 9, 26, 4, 27, 9, 27, 4, 28, 9, 28, 4,
	29, 9, 29, 4, 30, 9, 30, 4, 31, 9, 31, 4, 32, 9, 32, 4, 33, 9, 33, 4, 34,
	9, 34, 4, 35, 9, 35, 4, 36, 9, 36, 4, 37, 9, 37, 4, 38, 9, 38, 4, 39, 9,
	39, 4, 40, 9, 40, 4, 41, 9, 41, 4, 42, 9, 42, 4, 43, 9, 43, 4, 44, 9, 44,
	3, 2, 3, 2, 3, 2, 3, 3, 3, 3, 7, 3, 94, 10, 3, 12, 3, 14, 3, 97, 11, 3,
	3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4,
	3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 5, 4, 118, 10, 4, 3, 5, 3, 5,
	3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5,
	3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5,
	3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5,
	3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 5, 5, 166, 10, 5, 3, 5,
	3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 7, 5, 174, 10, 5, 12, 5, 14, 5, 177, 11,
	5, 3, 6, 3, 6, 3, 6, 3, 6, 3, 6, 3, 6, 3, 6, 5, 6, 186, 10, 6, 3, 7, 3,
	7, 3, 7, 3, 7, 3, 7, 3, 7, 5, 7, 194, 10, 7, 3, 7, 3, 7, 3, 7, 3, 7, 3,
	7, 3, 7, 3, 7, 3, 7, 7, 7, 204, 10, 7, 12, 7, 14, 7, 207, 11, 7, 3, 8,
	3, 8, 3, 8, 5, 8, 212, 10, 8, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9,
	3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9, 3, 9,
	3, 9, 3, 9, 7, 9, 235, 10, 9, 12, 9, 14, 9, 238, 11, 9, 3, 10, 3, 10, 3,
	10, 3, 10, 3, 10, 3, 10, 3, 10, 3, 10, 5, 10, 248, 10, 10, 3, 11, 3, 11,
	3, 11, 5, 11, 253, 10, 11, 3, 12, 3, 12, 3, 13, 3, 13, 3, 14, 3, 14, 3,
	14, 3, 14, 3, 15, 3, 15, 3, 15, 3, 16, 3, 16, 3, 16, 3, 17, 3, 17, 3, 17,
	3, 18, 3, 18, 3, 18, 5, 18, 275, 10, 18, 5, 18, 277, 10, 18, 3, 18, 3,
	18, 3, 19, 3, 19, 3, 19, 7, 19, 284, 10, 19, 12, 19, 14, 19, 287, 11, 19,
	3, 20, 3, 20, 3, 20, 5, 20, 292, 10, 20, 3, 20, 3, 20, 3, 21, 3, 21, 3,
	21, 5, 21, 299, 10, 21, 3, 22, 3, 22, 5, 22, 303, 10, 22, 3, 23, 3, 23,
	3, 23, 3, 23, 3, 23, 3, 23, 3, 23, 3, 23, 5, 23, 313, 10, 23, 3, 24, 3,
	24, 3, 25, 3, 25, 5, 25, 319, 10, 25, 3, 26, 3, 26, 5, 26, 323, 10, 26,
	3, 27, 3, 27, 3, 27, 3, 28, 3, 28, 3, 29, 3, 29, 3, 29, 3, 29, 3, 30, 3,
	30, 3, 30, 3, 30, 3, 31, 3, 31, 3, 31, 3, 31, 3, 31, 3, 31, 3, 31, 3, 31,
	3, 31, 3, 31, 3, 31, 3, 31, 3, 31, 5, 31, 351, 10, 31, 3, 32, 3, 32, 3,
	32, 3, 33, 3, 33, 3, 33, 7, 33, 359, 10, 33, 12, 33, 14, 33, 362, 11, 33,
	3, 33, 5, 33, 365, 10, 33, 3, 34, 3, 34, 3, 34, 7, 34, 370, 10, 34, 12,
	34, 14, 34, 373, 11, 34, 3, 35, 3, 35, 3, 35, 7, 35, 378, 10, 35, 12, 35,
	14, 35, 381, 11, 35, 3, 36, 3, 36, 3, 36, 7, 36, 386, 10, 36, 12, 36, 14,
	36, 389, 11, 36, 3, 36, 3, 36, 3, 37, 3, 37, 3, 37, 3, 37, 3, 37, 3, 37,
	3, 37, 3, 37, 3, 37, 3, 37, 5, 37, 403, 10, 37, 3, 38, 3, 38, 3, 38, 3,
	39, 3, 39, 3, 39, 3, 39, 3, 39, 3, 39, 5, 39, 414, 10, 39, 3, 39, 3, 39,
	3, 39, 3, 39, 3, 39, 3, 39, 7, 39, 422, 10, 39, 12, 39, 14, 39, 425, 11,
	39, 3, 40, 3, 40, 5, 40, 429, 10, 40, 3, 41, 3, 41, 3, 41, 3, 41, 3, 41,
	3, 41, 3, 42, 3, 42, 3, 42, 3, 42, 3, 42, 3, 42, 3, 42, 3, 42, 3, 42, 3,
	42, 3, 42, 3, 42, 3, 42, 3, 42, 3, 42, 5, 42, 452, 10, 42, 3, 43, 3, 43,
	3, 43, 3, 43, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3,
	44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 3, 44, 5, 44, 475,
	10, 44, 3, 44, 2, 6, 8, 12, 16, 76, 45, 2, 4, 6, 8, 10, 12, 14, 16, 18,
	20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54,
	56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 2, 8, 4,
	2, 26, 26, 41, 43, 4, 2, 36, 37, 43, 43, 3, 2, 41, 42, 3, 2, 32, 35, 3,
	2, 30, 31, 4, 2, 32, 32, 34, 34, 2, 498, 2, 88, 3, 2, 2, 2, 4, 91, 3, 2,
	2, 2, 6, 117, 3, 2, 2, 2, 8, 165, 3, 2, 2, 2, 10, 185, 3, 2, 2, 2, 12,
	187, 3, 2, 2, 2, 14, 211, 3, 2, 2, 2, 16, 213, 3, 2, 2, 2, 18, 247, 3,
	2, 2, 2, 20, 252, 3, 2, 2, 2, 22, 254, 3, 2, 2, 2, 24, 256, 3, 2, 2, 2,
	26, 258, 3, 2, 2, 2, 28, 262, 3, 2, 2, 2, 30, 265, 3, 2, 2, 2, 32, 268,
	3, 2, 2, 2, 34, 271, 3, 2, 2, 2, 36, 280, 3, 2, 2, 2, 38, 291, 3, 2, 2,
	2, 40, 298, 3, 2, 2, 2, 42, 302, 3, 2, 2, 2, 44, 312, 3, 2, 2, 2, 46, 314,
	3, 2, 2, 2, 48, 318, 3, 2, 2, 2, 50, 322, 3, 2, 2, 2, 52, 324, 3, 2, 2,
	2, 54, 327, 3, 2, 2, 2, 56, 329, 3, 2, 2, 2, 58, 333, 3, 2, 2, 2, 60, 350,
	3, 2, 2, 2, 62, 352, 3, 2, 2, 2, 64, 355, 3, 2, 2, 2, 66, 366, 3, 2, 2,
	2, 68, 374, 3, 2, 2, 2, 70, 382, 3, 2, 2, 2, 72, 402, 3, 2, 2, 2, 74, 404,
	3, 2, 2, 2, 76, 413, 3, 2, 2, 2, 78, 428, 3, 2, 2, 2, 80, 430, 3, 2, 2,
	2, 82, 451, 3, 2, 2, 2, 84, 453, 3, 2, 2, 2, 86, 474, 3, 2, 2, 2, 88, 89,
	5, 4, 3, 2, 89, 90, 7, 2, 2, 3, 90, 3, 3, 2, 2, 2, 91, 95, 5, 6, 4, 2,
	92, 94, 5, 6, 4, 2, 93, 92, 3, 2, 2, 2, 94, 97, 3, 2, 2, 2, 95, 93, 3,
	2, 2, 2, 95, 96, 3, 2, 2, 2, 96, 5, 3, 2, 2, 2, 97, 95, 3, 2, 2, 2, 98,
	99, 7, 20, 2, 2, 99, 100, 5, 6, 4, 2, 100, 101, 7, 21, 2, 2, 101, 118,
	3, 2, 2, 2, 102, 103, 7, 3, 2, 2, 103, 118, 5, 8, 5, 2, 104, 105, 7, 4,
	2, 2, 105, 118, 5, 8, 5, 2, 106, 107, 7, 5, 2, 2, 107, 118, 5, 8, 5, 2,
	108, 109, 7, 6, 2, 2, 109, 118, 5, 8, 5, 2, 110, 111, 7, 7, 2, 2, 111,
	118, 5, 8, 5, 2, 112, 118, 5, 54, 28, 2, 113, 118, 5, 62, 32, 2, 114, 118,
	5, 56, 29, 2, 115, 118, 5, 58, 30, 2, 116, 118, 5, 86, 44, 2, 117, 98,
	3, 2, 2, 2, 117, 102, 3, 2, 2, 2, 117, 104, 3, 2, 2, 2, 117, 106, 3, 2,
	2, 2, 117, 108, 3, 2, 2, 2, 117, 110, 3, 2, 2, 2, 117, 112, 3, 2, 2, 2,
	117, 113, 3, 2, 2, 2, 117, 114, 3, 2, 2, 2, 117, 115, 3, 2, 2, 2, 117,
	116, 3, 2, 2, 2, 118, 7, 3, 2, 2, 2, 119, 120, 8, 5, 1, 2, 120, 121, 7,
	20, 2, 2, 121, 122, 5, 8, 5, 2, 122, 123, 7, 21, 2, 2, 123, 166, 3, 2,
	2, 2, 124, 125, 7, 10, 2, 2, 125, 126, 5, 64, 33, 2, 126, 127, 7, 39, 2,
	2, 127, 128, 7, 39, 2, 2, 128, 129, 5, 76, 39, 2, 129, 130, 7, 29, 2, 2,
	130, 131, 5, 8, 5, 12, 131, 166, 3, 2, 2, 2, 132, 133, 7, 11, 2, 2, 133,
	134, 5, 64, 33, 2, 134, 135, 7, 39, 2, 2, 135, 136, 7, 39, 2, 2, 136, 137,
	5, 76, 39, 2, 137, 138, 7, 27, 2, 2, 138, 139, 5, 10, 6, 2, 139, 166, 3,
	2, 2, 2, 140, 141, 7, 10, 2, 2, 141, 142, 5, 64, 33, 2, 142, 143, 7, 39,
	2, 2, 143, 144, 7, 39, 2, 2, 144, 145, 5, 8, 5, 10, 145, 166, 3, 2, 2,
	2, 146, 147, 7, 11, 2, 2, 147, 148, 5, 64, 33, 2, 148, 149, 7, 39, 2, 2,
	149, 150, 7, 39, 2, 2, 150, 151, 5, 10, 6, 2, 151, 166, 3, 2, 2, 2, 152,
	166, 5, 10, 6, 2, 153, 154, 7, 26, 2, 2, 154, 166, 5, 8, 5, 7, 155, 156,
	5, 10, 6, 2, 156, 157, 7, 29, 2, 2, 157, 158, 5, 8, 5, 4, 158, 166, 3,
	2, 2, 2, 159, 160, 5, 10, 6, 2, 160, 161, 7, 44, 2, 2, 161, 162, 5, 8,
	5, 2, 162, 163, 7, 39, 2, 2, 163, 164, 5, 8, 5, 3, 164, 166, 3, 2, 2, 2,
	165, 119, 3, 2, 2, 2, 165, 124, 3, 2, 2, 2, 165, 132, 3, 2, 2, 2, 165,
	140, 3, 2, 2, 2, 165, 146, 3, 2, 2, 2, 165, 152, 3, 2, 2, 2, 165, 153,
	3, 2, 2, 2, 165, 155, 3, 2, 2, 2, 165, 159, 3, 2, 2, 2, 166, 175, 3, 2,
	2, 2, 167, 168, 12, 6, 2, 2, 168, 169, 7, 27, 2, 2, 169, 174, 5, 8, 5,
	7, 170, 171, 12, 5, 2, 2, 171, 172, 7, 28, 2, 2, 172, 174, 5, 8, 5, 6,
	173, 167, 3, 2, 2, 2, 173, 170, 3, 2, 2, 2, 174, 177, 3, 2, 2, 2, 175,
	173, 3, 2, 2, 2, 175, 176, 3, 2, 2, 2, 176, 9, 3, 2, 2, 2, 177, 175, 3,
	2, 2, 2, 178, 179, 7, 20, 2, 2, 179, 180, 5, 10, 6, 2, 180, 181, 7, 21,
	2, 2, 181, 186, 3, 2, 2, 2, 182, 186, 5, 12, 7, 2, 183, 186, 5, 14, 8,
	2, 184, 186, 5, 16, 9, 2, 185, 178, 3, 2, 2, 2, 185, 182, 3, 2, 2, 2, 185,
	183, 3, 2, 2, 2, 185, 184, 3, 2, 2, 2, 186, 11, 3, 2, 2, 2, 187, 188, 8,
	7, 1, 2, 188, 189, 5, 18, 10, 2, 189, 205, 3, 2, 2, 2, 190, 193, 12, 5,
	2, 2, 191, 194, 5, 28, 15, 2, 192, 194, 5, 26, 14, 2, 193, 191, 3, 2, 2,
	2, 193, 192, 3, 2, 2, 2, 194, 204, 3, 2, 2, 2, 195, 196, 12, 4, 2, 2, 196,
	197, 7, 20, 2, 2, 197, 198, 5, 66, 34, 2, 198, 199, 7, 21, 2, 2, 199, 204,
	3, 2, 2, 2, 200, 201, 12, 3, 2, 2, 201, 202, 7, 20, 2, 2, 202, 204, 7,
	21, 2, 2, 203, 190, 3, 2, 2, 2, 203, 195, 3, 2, 2, 2, 203, 200, 3, 2, 2,
	2, 204, 207, 3, 2, 2, 2, 205, 203, 3, 2, 2, 2, 205, 206, 3, 2, 2, 2, 206,
	13, 3, 2, 2, 2, 207, 205, 3, 2, 2, 2, 208, 212, 5, 12, 7, 2, 209, 210,
	9, 2, 2, 2, 210, 212, 5, 14, 8, 2, 211, 208, 3, 2, 2, 2, 211, 209, 3, 2,
	2, 2, 212, 15, 3, 2, 2, 2, 213, 214, 8, 9, 1, 2, 214, 215, 5, 14, 8, 2,
	215, 236, 3, 2, 2, 2, 216, 217, 12, 9, 2, 2, 217, 218, 9, 3, 2, 2, 218,
	235, 5, 16, 9, 10, 219, 220, 12, 8, 2, 2, 220, 221, 9, 4, 2, 2, 221, 235,
	5, 16, 9, 9, 222, 223, 12, 7, 2, 2, 223, 224, 9, 5, 2, 2, 224, 235, 5,
	16, 9, 8, 225, 226, 12, 6, 2, 2, 226, 227, 9, 6, 2, 2, 227, 235, 5, 16,
	9, 7, 228, 229, 12, 5, 2, 2, 229, 230, 7, 27, 2, 2, 230, 235, 5, 16, 9,
	6, 231, 232, 12, 4, 2, 2, 232, 233, 7, 28, 2, 2, 233, 235, 5, 16, 9, 5,
	234, 216, 3, 2, 2, 2, 234, 219, 3, 2, 2, 2, 234, 222, 3, 2, 2, 2, 234,
	225, 3, 2, 2, 2, 234, 228, 3, 2, 2, 2, 234, 231, 3, 2, 2, 2, 235, 238,
	3, 2, 2, 2, 236, 234, 3, 2, 2, 2, 236, 237, 3, 2, 2, 2, 237, 17, 3, 2,
	2, 2, 238, 236, 3, 2, 2, 2, 239, 248, 5, 20, 11, 2, 240, 248, 5, 24, 13,
	2, 241, 248, 5, 60, 31, 2, 242, 248, 5, 72, 37, 2, 243, 244, 7, 20, 2,
	2, 244, 245, 5, 10, 6, 2, 245, 246, 7, 21, 2, 2, 246, 248, 3, 2, 2, 2,
	247, 239, 3, 2, 2, 2, 247, 240, 3, 2, 2, 2, 247, 241, 3, 2, 2, 2, 247,
	242, 3, 2, 2, 2, 247, 243, 3, 2, 2, 2, 248, 19, 3, 2, 2, 2, 249, 253, 5,
	22, 12, 2, 250, 253, 5, 30, 16, 2, 251, 253, 5, 32, 17, 2, 252, 249, 3,
	2, 2, 2, 252, 250, 3, 2, 2, 2, 252, 251, 3, 2, 2, 2, 253, 21, 3, 2, 2,
	2, 254, 255, 7, 19, 2, 2, 255, 23, 3, 2, 2, 2, 256, 257, 7, 18, 2, 2, 257,
	25, 3, 2, 2, 2, 258, 259, 7, 22, 2, 2, 259, 260, 5, 10, 6, 2, 260, 261,
	7, 23, 2, 2, 261, 27, 3, 2, 2, 2, 262, 263, 7, 38, 2, 2, 263, 264, 5, 24,
	13, 2, 264, 29, 3, 2, 2, 2, 265, 266, 5, 44, 23, 2, 266, 267, 5, 34, 18,
	2, 267, 31, 3, 2, 2, 2, 268, 269, 5, 24, 13, 2, 269, 270, 5, 34, 18, 2,
	270, 33, 3, 2, 2, 2, 271, 276, 7, 24, 2, 2, 272, 274, 5, 36, 19, 2, 273,
	275, 7, 40, 2, 2, 274, 273, 3, 2, 2, 2, 274, 275, 3, 2, 2, 2, 275, 277,
	3, 2, 2, 2, 276, 272, 3, 2, 2, 2, 276, 277, 3, 2, 2, 2, 277, 278, 3, 2,
	2, 2, 278, 279, 7, 25, 2, 2, 279, 35, 3, 2, 2, 2, 280, 285, 5, 38, 20,
	2, 281, 282, 7, 40, 2, 2, 282, 284, 5, 38, 20, 2, 283, 281, 3, 2, 2, 2,
	284, 287, 3, 2, 2, 2, 285, 283, 3, 2, 2, 2, 285, 286, 3, 2, 2, 2, 286,
	37, 3, 2, 2, 2, 287, 285, 3, 2, 2, 2, 288, 289, 5, 40, 21, 2, 289, 290,
	7, 39, 2, 2, 290, 292, 3, 2, 2, 2, 291, 288, 3, 2, 2, 2, 291, 292, 3, 2,
	2, 2, 292, 293, 3, 2, 2, 2, 293, 294, 5, 42, 22, 2, 294, 39, 3, 2, 2, 2,
	295, 299, 5, 24, 13, 2, 296, 299, 5, 10, 6, 2, 297, 299, 5, 34, 18, 2,
	298, 295, 3, 2, 2, 2, 298, 296, 3, 2, 2, 2, 298, 297, 3, 2, 2, 2, 299,
	41, 3, 2, 2, 2, 300, 303, 5, 10, 6, 2, 301, 303, 5, 34, 18, 2, 302, 300,
	3, 2, 2, 2, 302, 301, 3, 2, 2, 2, 303, 43, 3, 2, 2, 2, 304, 305, 7, 22,
	2, 2, 305, 306, 5, 46, 24, 2, 306, 307, 7, 23, 2, 2, 307, 308, 5, 48, 25,
	2, 308, 313, 3, 2, 2, 2, 309, 310, 7, 22, 2, 2, 310, 311, 7, 23, 2, 2,
	311, 313, 5, 48, 25, 2, 312, 304, 3, 2, 2, 2, 312, 309, 3, 2, 2, 2, 313,
	45, 3, 2, 2, 2, 314, 315, 5, 10, 6, 2, 315, 47, 3, 2, 2, 2, 316, 319, 5,
	24, 13, 2, 317, 319, 5, 50, 26, 2, 318, 316, 3, 2, 2, 2, 318, 317, 3, 2,
	2, 2, 319, 49, 3, 2, 2, 2, 320, 323, 5, 44, 23, 2, 321, 323, 5, 52, 27,
	2, 322, 320, 3, 2, 2, 2, 322, 321, 3, 2, 2, 2, 323, 51, 3, 2, 2, 2, 324,
	325, 7, 43, 2, 2, 325, 326, 5, 48, 25, 2, 326, 53, 3, 2, 2, 2, 327, 328,
	7, 8, 2, 2, 328, 55, 3, 2, 2, 2, 329, 330, 7, 15, 2, 2, 330, 331, 7, 39,
	2, 2, 331, 332, 5, 68, 35, 2, 332, 57, 3, 2, 2, 2, 333, 334, 7, 16, 2,
	2, 334, 335, 7, 39, 2, 2, 335, 336, 5, 68, 35, 2, 336, 59, 3, 2, 2, 2,
	337, 338, 7, 9, 2, 2, 338, 339, 7, 20, 2, 2, 339, 340, 5, 10, 6, 2, 340,
	341, 7, 21, 2, 2, 341, 351, 3, 2, 2, 2, 342, 343, 7, 9, 2, 2, 343, 344,
	7, 22, 2, 2, 344, 345, 5, 24, 13, 2, 345, 346, 7, 23, 2, 2, 346, 347, 7,
	20, 2, 2, 347, 348, 5, 10, 6, 2, 348, 349, 7, 21, 2, 2, 349, 351, 3, 2,
	2, 2, 350, 337, 3, 2, 2, 2, 350, 342, 3, 2, 2, 2, 351, 61, 3, 2, 2, 2,
	352, 353, 5, 24, 13, 2, 353, 354, 7, 39, 2, 2, 354, 63, 3, 2, 2, 2, 355,
	360, 5, 70, 36, 2, 356, 357, 7, 40, 2, 2, 357, 359, 5, 70, 36, 2, 358,
	356, 3, 2, 2, 2, 359, 362, 3, 2, 2, 2, 360, 358, 3, 2, 2, 2, 360, 361,
	3, 2, 2, 2, 361, 364, 3, 2, 2, 2, 362, 360, 3, 2, 2, 2, 363, 365, 7, 40,
	2, 2, 364, 363, 3, 2, 2, 2, 364, 365, 3, 2, 2, 2, 365, 65, 3, 2, 2, 2,
	366, 371, 5, 10, 6, 2, 367, 368, 7, 40, 2, 2, 368, 370, 5, 10, 6, 2, 369,
	367, 3, 2, 2, 2, 370, 373, 3, 2, 2, 2, 371, 369, 3, 2, 2, 2, 371, 372,
	3, 2, 2, 2, 372, 67, 3, 2, 2, 2, 373, 371, 3, 2, 2, 2, 374, 379, 5, 24,
	13, 2, 375, 376, 7, 40, 2, 2, 376, 378, 5, 24, 13, 2, 377, 375, 3, 2, 2,
	2, 378, 381, 3, 2, 2, 2, 379, 377, 3, 2, 2, 2, 379, 380, 3, 2, 2, 2, 380,
	69, 3, 2, 2, 2, 381, 379, 3, 2, 2, 2, 382, 387, 5, 24, 13, 2, 383, 384,
	7, 40, 2, 2, 384, 386, 5, 24, 13, 2, 385, 383, 3, 2, 2, 2, 386, 389, 3,
	2, 2, 2, 387, 385, 3, 2, 2, 2, 387, 388, 3, 2, 2, 2, 388, 390, 3, 2, 2,
	2, 389, 387, 3, 2, 2, 2, 390, 391, 5, 48, 25, 2, 391, 71, 3, 2, 2, 2, 392,
	393, 7, 12, 2, 2, 393, 394, 7, 20, 2, 2, 394, 395, 5, 12, 7, 2, 395, 396,
	7, 21, 2, 2, 396, 403, 3, 2, 2, 2, 397, 398, 7, 12, 2, 2, 398, 399, 7,
	20, 2, 2, 399, 400, 5, 74, 38, 2, 400, 401, 7, 21, 2, 2, 401, 403, 3, 2,
	2, 2, 402, 392, 3, 2, 2, 2, 402, 397, 3, 2, 2, 2, 403, 73, 3, 2, 2, 2,
	404, 405, 7, 45, 2, 2, 405, 406, 5, 12, 7, 2, 406, 75, 3, 2, 2, 2, 407,
	408, 8, 39, 1, 2, 408, 409, 7, 20, 2, 2, 409, 410, 5, 76, 39, 2, 410, 411,
	7, 21, 2, 2, 411, 414, 3, 2, 2, 2, 412, 414, 5, 78, 40, 2, 413, 407, 3,
	2, 2, 2, 413, 412, 3, 2, 2, 2, 414, 423, 3, 2, 2, 2, 415, 416, 12, 5, 2,
	2, 416, 417, 7, 27, 2, 2, 417, 422, 5, 76, 39, 6, 418, 419, 12, 4, 2, 2,
	419, 420, 7, 28, 2, 2, 420, 422, 5, 76, 39, 5, 421, 415, 3, 2, 2, 2, 421,
	418, 3, 2, 2, 2, 422, 425, 3, 2, 2, 2, 423, 421, 3, 2, 2, 2, 423, 424,
	3, 2, 2, 2, 424, 77, 3, 2, 2, 2, 425, 423, 3, 2, 2, 2, 426, 429, 5, 80,
	41, 2, 427, 429, 5, 82, 42, 2, 428, 426, 3, 2, 2, 2, 428, 427, 3, 2, 2,
	2, 429, 79, 3, 2, 2, 2, 430, 431, 5, 10, 6, 2, 431, 432, 9, 7, 2, 2, 432,
	433, 5, 24, 13, 2, 433, 434, 9, 7, 2, 2, 434, 435, 5, 10, 6, 2, 435, 81,
	3, 2, 2, 2, 436, 437, 7, 20, 2, 2, 437, 438, 5, 24, 13, 2, 438, 439, 7,
	40, 2, 2, 439, 440, 5, 24, 13, 2, 440, 441, 7, 21, 2, 2, 441, 442, 5, 84,
	43, 2, 442, 452, 3, 2, 2, 2, 443, 444, 5, 24, 13, 2, 444, 445, 7, 40, 2,
	2, 445, 446, 5, 24, 13, 2, 446, 447, 5, 84, 43, 2, 447, 452, 3, 2, 2, 2,
	448, 449, 5, 24, 13, 2, 449, 450, 5, 84, 43, 2, 450, 452, 3, 2, 2, 2, 451,
	436, 3, 2, 2, 2, 451, 443, 3, 2, 2, 2, 451, 448, 3, 2, 2, 2, 452, 83, 3,
	2, 2, 2, 453, 454, 7, 13, 2, 2, 454, 455, 7, 14, 2, 2, 455, 456, 5, 10,
	6, 2, 456, 85, 3, 2, 2, 2, 457, 458, 7, 17, 2, 2, 458, 459, 5, 24, 13,
	2, 459, 460, 7, 20, 2, 2, 460, 461, 5, 64, 33, 2, 461, 462, 7, 21, 2, 2,
	462, 463, 7, 24, 2, 2, 463, 464, 5, 8, 5, 2, 464, 465, 7, 25, 2, 2, 465,
	475, 3, 2, 2, 2, 466, 467, 7, 17, 2, 2, 467, 468, 5, 24, 13, 2, 468, 469,
	7, 20, 2, 2, 469, 470, 7, 21, 2, 2, 470, 471, 7, 24, 2, 2, 471, 472, 5,
	8, 5, 2, 472, 473, 7, 25, 2, 2, 473, 475, 3, 2, 2, 2, 474, 457, 3, 2, 2,
	2, 474, 466, 3, 2, 2, 2, 475, 87, 3, 2, 2, 2, 38, 95, 117, 165, 173, 175,
	185, 193, 203, 205, 211, 234, 236, 247, 252, 274, 276, 285, 291, 298, 302,
	312, 318, 322, 350, 360, 364, 371, 379, 387, 402, 413, 421, 423, 428, 451,
	474,
}
var deserializer = antlr.NewATNDeserializer(nil)
var deserializedATN = deserializer.DeserializeFromUInt16(parserATN)

var literalNames = []string{
	"", "'assert'", "'assume'", "'requires'", "'ensures'", "'invariant'", "'pure'",
	"'old'", "'forall'", "'exists'", "'acc'", "'in'", "'range'", "'shared'",
	"'exclusive'", "'predicate'", "", "", "'('", "')'", "'['", "']'", "'{'",
	"'}'", "'!'", "'&&'", "'||'", "'==>'", "'=='", "'!='", "'<'", "'>'", "'<='",
	"'>='", "'/'", "'%'", "'.'", "':'", "','", "'+'", "'-'", "'*'", "'?'",
	"'&'", "", "'/*@'", "'@*/'", "'//@'",
}
var symbolicNames = []string{
	"", "ASSERT", "ASSUME", "PRE", "POST", "INV", "PURE", "OLD", "FORALL",
	"EXISTS", "ACCESS", "IN", "RANGE", "SHARED", "EXCLUSIVE", "PREDICATE",
	"IDENTIFIER", "INTEGER", "LPAREN", "RPAREN", "LSB", "RSB", "LCB", "RCB",
	"NOT", "AND", "OR", "IMPLIES", "EQ", "NEQ", "LESS", "GREAT", "LEQ", "GEQ",
	"DIV", "MOD", "DOT", "COLON", "COMMA", "PLUS", "MINUS", "STAR", "QUESTION",
	"REFERENCE", "WHITESPACE", "SPECSTART", "SPECEND", "SPECLINESTART",
}

var ruleNames = []string{
	"start", "specification", "specStatement", "assertion", "expression", "primary",
	"unary", "binary", "operand", "literal", "integer", "identifier", "squarebracket",
	"dotnotation", "arrayLit", "structLit", "literalValue", "elementList",
	"keyedElement", "key", "element", "arrayType", "arrayLength", "elementType",
	"typeLit", "pointerType", "purity", "sharedVarsNotation", "exclusiveVarsNotation",
	"old", "label", "variableList", "expressionList", "identifierList", "varTypeTuple",
	"accessPermission", "reference", "domain", "domainLiteral", "numericDomainLiteral",
	"dataStructureDomainLiteral", "dataStructureRange", "predicate",
}
var decisionToDFA = make([]*antlr.DFA, len(deserializedATN.DecisionToState))

func init() {
	for index, ds := range deserializedATN.DecisionToState {
		decisionToDFA[index] = antlr.NewDFA(ds, index)
	}
}

type SpecGrammarParser struct {
	*antlr.BaseParser
}

func NewSpecGrammarParser(input antlr.TokenStream) *SpecGrammarParser {
	this := new(SpecGrammarParser)

	this.BaseParser = antlr.NewBaseParser(input)

	this.Interpreter = antlr.NewParserATNSimulator(this, deserializedATN, decisionToDFA, antlr.NewPredictionContextCache())
	this.RuleNames = ruleNames
	this.LiteralNames = literalNames
	this.SymbolicNames = symbolicNames
	this.GrammarFileName = "SpecGrammar.g4"

	return this
}

// SpecGrammarParser tokens.
const (
	SpecGrammarParserEOF           = antlr.TokenEOF
	SpecGrammarParserASSERT        = 1
	SpecGrammarParserASSUME        = 2
	SpecGrammarParserPRE           = 3
	SpecGrammarParserPOST          = 4
	SpecGrammarParserINV           = 5
	SpecGrammarParserPURE          = 6
	SpecGrammarParserOLD           = 7
	SpecGrammarParserFORALL        = 8
	SpecGrammarParserEXISTS        = 9
	SpecGrammarParserACCESS        = 10
	SpecGrammarParserIN            = 11
	SpecGrammarParserRANGE         = 12
	SpecGrammarParserSHARED        = 13
	SpecGrammarParserEXCLUSIVE     = 14
	SpecGrammarParserPREDICATE     = 15
	SpecGrammarParserIDENTIFIER    = 16
	SpecGrammarParserINTEGER       = 17
	SpecGrammarParserLPAREN        = 18
	SpecGrammarParserRPAREN        = 19
	SpecGrammarParserLSB           = 20
	SpecGrammarParserRSB           = 21
	SpecGrammarParserLCB           = 22
	SpecGrammarParserRCB           = 23
	SpecGrammarParserNOT           = 24
	SpecGrammarParserAND           = 25
	SpecGrammarParserOR            = 26
	SpecGrammarParserIMPLIES       = 27
	SpecGrammarParserEQ            = 28
	SpecGrammarParserNEQ           = 29
	SpecGrammarParserLESS          = 30
	SpecGrammarParserGREAT         = 31
	SpecGrammarParserLEQ           = 32
	SpecGrammarParserGEQ           = 33
	SpecGrammarParserDIV           = 34
	SpecGrammarParserMOD           = 35
	SpecGrammarParserDOT           = 36
	SpecGrammarParserCOLON         = 37
	SpecGrammarParserCOMMA         = 38
	SpecGrammarParserPLUS          = 39
	SpecGrammarParserMINUS         = 40
	SpecGrammarParserSTAR          = 41
	SpecGrammarParserQUESTION      = 42
	SpecGrammarParserREFERENCE     = 43
	SpecGrammarParserWHITESPACE    = 44
	SpecGrammarParserSPECSTART     = 45
	SpecGrammarParserSPECEND       = 46
	SpecGrammarParserSPECLINESTART = 47
)

// SpecGrammarParser rules.
const (
	SpecGrammarParserRULE_start                      = 0
	SpecGrammarParserRULE_specification              = 1
	SpecGrammarParserRULE_specStatement              = 2
	SpecGrammarParserRULE_assertion                  = 3
	SpecGrammarParserRULE_expression                 = 4
	SpecGrammarParserRULE_primary                    = 5
	SpecGrammarParserRULE_unary                      = 6
	SpecGrammarParserRULE_binary                     = 7
	SpecGrammarParserRULE_operand                    = 8
	SpecGrammarParserRULE_literal                    = 9
	SpecGrammarParserRULE_integer                    = 10
	SpecGrammarParserRULE_identifier                 = 11
	SpecGrammarParserRULE_squarebracket              = 12
	SpecGrammarParserRULE_dotnotation                = 13
	SpecGrammarParserRULE_arrayLit                   = 14
	SpecGrammarParserRULE_structLit                  = 15
	SpecGrammarParserRULE_literalValue               = 16
	SpecGrammarParserRULE_elementList                = 17
	SpecGrammarParserRULE_keyedElement               = 18
	SpecGrammarParserRULE_key                        = 19
	SpecGrammarParserRULE_element                    = 20
	SpecGrammarParserRULE_arrayType                  = 21
	SpecGrammarParserRULE_arrayLength                = 22
	SpecGrammarParserRULE_elementType                = 23
	SpecGrammarParserRULE_typeLit                    = 24
	SpecGrammarParserRULE_pointerType                = 25
	SpecGrammarParserRULE_purity                     = 26
	SpecGrammarParserRULE_sharedVarsNotation         = 27
	SpecGrammarParserRULE_exclusiveVarsNotation      = 28
	SpecGrammarParserRULE_old                        = 29
	SpecGrammarParserRULE_label                      = 30
	SpecGrammarParserRULE_variableList               = 31
	SpecGrammarParserRULE_expressionList             = 32
	SpecGrammarParserRULE_identifierList             = 33
	SpecGrammarParserRULE_varTypeTuple               = 34
	SpecGrammarParserRULE_accessPermission           = 35
	SpecGrammarParserRULE_reference                  = 36
	SpecGrammarParserRULE_domain                     = 37
	SpecGrammarParserRULE_domainLiteral              = 38
	SpecGrammarParserRULE_numericDomainLiteral       = 39
	SpecGrammarParserRULE_dataStructureDomainLiteral = 40
	SpecGrammarParserRULE_dataStructureRange         = 41
	SpecGrammarParserRULE_predicate                  = 42
)

// IStartContext is an interface to support dynamic dispatch.
type IStartContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsStartContext differentiates from other interfaces.
	IsStartContext()
}

type StartContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyStartContext() *StartContext {
	var p = new(StartContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_start
	return p
}

func (*StartContext) IsStartContext() {}

func NewStartContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *StartContext {
	var p = new(StartContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_start

	return p
}

func (s *StartContext) GetParser() antlr.Parser { return s.parser }

func (s *StartContext) Specification() ISpecificationContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ISpecificationContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ISpecificationContext)
}

func (s *StartContext) EOF() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserEOF, 0)
}

func (s *StartContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *StartContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *StartContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterStart(s)
	}
}

func (s *StartContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitStart(s)
	}
}

func (s *StartContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitStart(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Start() (localctx IStartContext) {
	localctx = NewStartContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 0, SpecGrammarParserRULE_start)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(86)
		p.Specification()
	}
	{
		p.SetState(87)
		p.Match(SpecGrammarParserEOF)
	}

	return localctx
}

// ISpecificationContext is an interface to support dynamic dispatch.
type ISpecificationContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsSpecificationContext differentiates from other interfaces.
	IsSpecificationContext()
}

type SpecificationContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptySpecificationContext() *SpecificationContext {
	var p = new(SpecificationContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_specification
	return p
}

func (*SpecificationContext) IsSpecificationContext() {}

func NewSpecificationContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *SpecificationContext {
	var p = new(SpecificationContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_specification

	return p
}

func (s *SpecificationContext) GetParser() antlr.Parser { return s.parser }

func (s *SpecificationContext) AllSpecStatement() []ISpecStatementContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*ISpecStatementContext)(nil)).Elem())
	var tst = make([]ISpecStatementContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(ISpecStatementContext)
		}
	}

	return tst
}

func (s *SpecificationContext) SpecStatement(i int) ISpecStatementContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ISpecStatementContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(ISpecStatementContext)
}

func (s *SpecificationContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *SpecificationContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *SpecificationContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterSpecification(s)
	}
}

func (s *SpecificationContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitSpecification(s)
	}
}

func (s *SpecificationContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitSpecification(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Specification() (localctx ISpecificationContext) {
	localctx = NewSpecificationContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 2, SpecGrammarParserRULE_specification)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(89)
		p.SpecStatement()
	}
	p.SetState(93)
	p.GetErrorHandler().Sync(p)
	_la = p.GetTokenStream().LA(1)

	for ((_la)&-(0x1f+1)) == 0 && ((1<<uint(_la))&((1<<SpecGrammarParserASSERT)|(1<<SpecGrammarParserASSUME)|(1<<SpecGrammarParserPRE)|(1<<SpecGrammarParserPOST)|(1<<SpecGrammarParserINV)|(1<<SpecGrammarParserPURE)|(1<<SpecGrammarParserSHARED)|(1<<SpecGrammarParserEXCLUSIVE)|(1<<SpecGrammarParserPREDICATE)|(1<<SpecGrammarParserIDENTIFIER)|(1<<SpecGrammarParserLPAREN))) != 0 {
		{
			p.SetState(90)
			p.SpecStatement()
		}

		p.SetState(95)
		p.GetErrorHandler().Sync(p)
		_la = p.GetTokenStream().LA(1)
	}

	return localctx
}

// ISpecStatementContext is an interface to support dynamic dispatch.
type ISpecStatementContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetKind returns the kind token.
	GetKind() antlr.Token

	// SetKind sets the kind token.
	SetKind(antlr.Token)

	// IsSpecStatementContext differentiates from other interfaces.
	IsSpecStatementContext()
}

type SpecStatementContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
	kind   antlr.Token
}

func NewEmptySpecStatementContext() *SpecStatementContext {
	var p = new(SpecStatementContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_specStatement
	return p
}

func (*SpecStatementContext) IsSpecStatementContext() {}

func NewSpecStatementContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *SpecStatementContext {
	var p = new(SpecStatementContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_specStatement

	return p
}

func (s *SpecStatementContext) GetParser() antlr.Parser { return s.parser }

func (s *SpecStatementContext) GetKind() antlr.Token { return s.kind }

func (s *SpecStatementContext) SetKind(v antlr.Token) { s.kind = v }

func (s *SpecStatementContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *SpecStatementContext) SpecStatement() ISpecStatementContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ISpecStatementContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ISpecStatementContext)
}

func (s *SpecStatementContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *SpecStatementContext) Assertion() IAssertionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IAssertionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IAssertionContext)
}

func (s *SpecStatementContext) ASSERT() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserASSERT, 0)
}

func (s *SpecStatementContext) ASSUME() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserASSUME, 0)
}

func (s *SpecStatementContext) PRE() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserPRE, 0)
}

func (s *SpecStatementContext) POST() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserPOST, 0)
}

func (s *SpecStatementContext) INV() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserINV, 0)
}

func (s *SpecStatementContext) Purity() IPurityContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPurityContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPurityContext)
}

func (s *SpecStatementContext) Label() ILabelContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ILabelContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ILabelContext)
}

func (s *SpecStatementContext) SharedVarsNotation() ISharedVarsNotationContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ISharedVarsNotationContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ISharedVarsNotationContext)
}

func (s *SpecStatementContext) ExclusiveVarsNotation() IExclusiveVarsNotationContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExclusiveVarsNotationContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExclusiveVarsNotationContext)
}

func (s *SpecStatementContext) Predicate() IPredicateContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPredicateContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPredicateContext)
}

func (s *SpecStatementContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *SpecStatementContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *SpecStatementContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterSpecStatement(s)
	}
}

func (s *SpecStatementContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitSpecStatement(s)
	}
}

func (s *SpecStatementContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitSpecStatement(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) SpecStatement() (localctx ISpecStatementContext) {
	localctx = NewSpecStatementContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 4, SpecGrammarParserRULE_specStatement)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(115)
	p.GetErrorHandler().Sync(p)

	switch p.GetTokenStream().LA(1) {
	case SpecGrammarParserLPAREN:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(96)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(97)
			p.SpecStatement()
		}
		{
			p.SetState(98)
			p.Match(SpecGrammarParserRPAREN)
		}

	case SpecGrammarParserASSERT:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(100)

			var _m = p.Match(SpecGrammarParserASSERT)

			localctx.(*SpecStatementContext).kind = _m
		}
		{
			p.SetState(101)
			p.assertion(0)
		}

	case SpecGrammarParserASSUME:
		p.EnterOuterAlt(localctx, 3)
		{
			p.SetState(102)

			var _m = p.Match(SpecGrammarParserASSUME)

			localctx.(*SpecStatementContext).kind = _m
		}
		{
			p.SetState(103)
			p.assertion(0)
		}

	case SpecGrammarParserPRE:
		p.EnterOuterAlt(localctx, 4)
		{
			p.SetState(104)

			var _m = p.Match(SpecGrammarParserPRE)

			localctx.(*SpecStatementContext).kind = _m
		}
		{
			p.SetState(105)
			p.assertion(0)
		}

	case SpecGrammarParserPOST:
		p.EnterOuterAlt(localctx, 5)
		{
			p.SetState(106)

			var _m = p.Match(SpecGrammarParserPOST)

			localctx.(*SpecStatementContext).kind = _m
		}
		{
			p.SetState(107)
			p.assertion(0)
		}

	case SpecGrammarParserINV:
		p.EnterOuterAlt(localctx, 6)
		{
			p.SetState(108)

			var _m = p.Match(SpecGrammarParserINV)

			localctx.(*SpecStatementContext).kind = _m
		}
		{
			p.SetState(109)
			p.assertion(0)
		}

	case SpecGrammarParserPURE:
		p.EnterOuterAlt(localctx, 7)
		{
			p.SetState(110)
			p.Purity()
		}

	case SpecGrammarParserIDENTIFIER:
		p.EnterOuterAlt(localctx, 8)
		{
			p.SetState(111)
			p.Label()
		}

	case SpecGrammarParserSHARED:
		p.EnterOuterAlt(localctx, 9)
		{
			p.SetState(112)
			p.SharedVarsNotation()
		}

	case SpecGrammarParserEXCLUSIVE:
		p.EnterOuterAlt(localctx, 10)
		{
			p.SetState(113)
			p.ExclusiveVarsNotation()
		}

	case SpecGrammarParserPREDICATE:
		p.EnterOuterAlt(localctx, 11)
		{
			p.SetState(114)
			p.Predicate()
		}

	default:
		panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
	}

	return localctx
}

// IAssertionContext is an interface to support dynamic dispatch.
type IAssertionContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetKind returns the kind token.
	GetKind() antlr.Token

	// SetKind sets the kind token.
	SetKind(antlr.Token)

	// IsAssertionContext differentiates from other interfaces.
	IsAssertionContext()
}

type AssertionContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
	kind   antlr.Token
}

func NewEmptyAssertionContext() *AssertionContext {
	var p = new(AssertionContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_assertion
	return p
}

func (*AssertionContext) IsAssertionContext() {}

func NewAssertionContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *AssertionContext {
	var p = new(AssertionContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_assertion

	return p
}

func (s *AssertionContext) GetParser() antlr.Parser { return s.parser }

func (s *AssertionContext) GetKind() antlr.Token { return s.kind }

func (s *AssertionContext) SetKind(v antlr.Token) { s.kind = v }

func (s *AssertionContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *AssertionContext) AllAssertion() []IAssertionContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IAssertionContext)(nil)).Elem())
	var tst = make([]IAssertionContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IAssertionContext)
		}
	}

	return tst
}

func (s *AssertionContext) Assertion(i int) IAssertionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IAssertionContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IAssertionContext)
}

func (s *AssertionContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *AssertionContext) FORALL() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserFORALL, 0)
}

func (s *AssertionContext) VariableList() IVariableListContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IVariableListContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IVariableListContext)
}

func (s *AssertionContext) AllCOLON() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserCOLON)
}

func (s *AssertionContext) COLON(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOLON, i)
}

func (s *AssertionContext) Domain() IDomainContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IDomainContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IDomainContext)
}

func (s *AssertionContext) IMPLIES() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserIMPLIES, 0)
}

func (s *AssertionContext) EXISTS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserEXISTS, 0)
}

func (s *AssertionContext) AND() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserAND, 0)
}

func (s *AssertionContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *AssertionContext) NOT() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserNOT, 0)
}

func (s *AssertionContext) QUESTION() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserQUESTION, 0)
}

func (s *AssertionContext) OR() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserOR, 0)
}

func (s *AssertionContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *AssertionContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *AssertionContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterAssertion(s)
	}
}

func (s *AssertionContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitAssertion(s)
	}
}

func (s *AssertionContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitAssertion(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Assertion() (localctx IAssertionContext) {
	return p.assertion(0)
}

func (p *SpecGrammarParser) assertion(_p int) (localctx IAssertionContext) {
	var _parentctx antlr.ParserRuleContext = p.GetParserRuleContext()
	_parentState := p.GetState()
	localctx = NewAssertionContext(p, p.GetParserRuleContext(), _parentState)
	var _prevctx IAssertionContext = localctx
	var _ antlr.ParserRuleContext = _prevctx // TODO: To prevent unused variable warning.
	_startState := 6
	p.EnterRecursionRule(localctx, 6, SpecGrammarParserRULE_assertion, _p)

	defer func() {
		p.UnrollRecursionContexts(_parentctx)
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	var _alt int

	p.EnterOuterAlt(localctx, 1)
	p.SetState(163)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 2, p.GetParserRuleContext()) {
	case 1:
		{
			p.SetState(118)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(119)
			p.assertion(0)
		}
		{
			p.SetState(120)
			p.Match(SpecGrammarParserRPAREN)
		}

	case 2:
		{
			p.SetState(122)
			p.Match(SpecGrammarParserFORALL)
		}
		{
			p.SetState(123)
			p.VariableList()
		}
		{
			p.SetState(124)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(125)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(126)
			p.domain(0)
		}
		{
			p.SetState(127)
			p.Match(SpecGrammarParserIMPLIES)
		}
		{
			p.SetState(128)
			p.assertion(10)
		}

	case 3:
		{
			p.SetState(130)
			p.Match(SpecGrammarParserEXISTS)
		}
		{
			p.SetState(131)
			p.VariableList()
		}
		{
			p.SetState(132)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(133)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(134)
			p.domain(0)
		}
		{
			p.SetState(135)
			p.Match(SpecGrammarParserAND)
		}
		{
			p.SetState(136)
			p.Expression()
		}

	case 4:
		{
			p.SetState(138)
			p.Match(SpecGrammarParserFORALL)
		}
		{
			p.SetState(139)
			p.VariableList()
		}
		{
			p.SetState(140)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(141)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(142)
			p.assertion(8)
		}

	case 5:
		{
			p.SetState(144)
			p.Match(SpecGrammarParserEXISTS)
		}
		{
			p.SetState(145)
			p.VariableList()
		}
		{
			p.SetState(146)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(147)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(148)
			p.Expression()
		}

	case 6:
		{
			p.SetState(150)
			p.Expression()
		}

	case 7:
		{
			p.SetState(151)

			var _m = p.Match(SpecGrammarParserNOT)

			localctx.(*AssertionContext).kind = _m
		}
		{
			p.SetState(152)
			p.assertion(5)
		}

	case 8:
		{
			p.SetState(153)
			p.Expression()
		}
		{
			p.SetState(154)

			var _m = p.Match(SpecGrammarParserIMPLIES)

			localctx.(*AssertionContext).kind = _m
		}
		{
			p.SetState(155)
			p.assertion(2)
		}

	case 9:
		{
			p.SetState(157)
			p.Expression()
		}
		{
			p.SetState(158)

			var _m = p.Match(SpecGrammarParserQUESTION)

			localctx.(*AssertionContext).kind = _m
		}
		{
			p.SetState(159)
			p.assertion(0)
		}
		{
			p.SetState(160)
			p.Match(SpecGrammarParserCOLON)
		}
		{
			p.SetState(161)
			p.assertion(1)
		}

	}
	p.GetParserRuleContext().SetStop(p.GetTokenStream().LT(-1))
	p.SetState(173)
	p.GetErrorHandler().Sync(p)
	_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 4, p.GetParserRuleContext())

	for _alt != 2 && _alt != antlr.ATNInvalidAltNumber {
		if _alt == 1 {
			if p.GetParseListeners() != nil {
				p.TriggerExitRuleEvent()
			}
			_prevctx = localctx
			p.SetState(171)
			p.GetErrorHandler().Sync(p)
			switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 3, p.GetParserRuleContext()) {
			case 1:
				localctx = NewAssertionContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_assertion)
				p.SetState(165)

				if !(p.Precpred(p.GetParserRuleContext(), 4)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 4)", ""))
				}
				{
					p.SetState(166)

					var _m = p.Match(SpecGrammarParserAND)

					localctx.(*AssertionContext).kind = _m
				}
				{
					p.SetState(167)
					p.assertion(5)
				}

			case 2:
				localctx = NewAssertionContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_assertion)
				p.SetState(168)

				if !(p.Precpred(p.GetParserRuleContext(), 3)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 3)", ""))
				}
				{
					p.SetState(169)

					var _m = p.Match(SpecGrammarParserOR)

					localctx.(*AssertionContext).kind = _m
				}
				{
					p.SetState(170)
					p.assertion(4)
				}

			}

		}
		p.SetState(175)
		p.GetErrorHandler().Sync(p)
		_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 4, p.GetParserRuleContext())
	}

	return localctx
}

// IExpressionContext is an interface to support dynamic dispatch.
type IExpressionContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsExpressionContext differentiates from other interfaces.
	IsExpressionContext()
}

type ExpressionContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyExpressionContext() *ExpressionContext {
	var p = new(ExpressionContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_expression
	return p
}

func (*ExpressionContext) IsExpressionContext() {}

func NewExpressionContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ExpressionContext {
	var p = new(ExpressionContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_expression

	return p
}

func (s *ExpressionContext) GetParser() antlr.Parser { return s.parser }

func (s *ExpressionContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *ExpressionContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *ExpressionContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *ExpressionContext) Primary() IPrimaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPrimaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPrimaryContext)
}

func (s *ExpressionContext) Unary() IUnaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IUnaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IUnaryContext)
}

func (s *ExpressionContext) Binary() IBinaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IBinaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IBinaryContext)
}

func (s *ExpressionContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ExpressionContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ExpressionContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterExpression(s)
	}
}

func (s *ExpressionContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitExpression(s)
	}
}

func (s *ExpressionContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitExpression(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Expression() (localctx IExpressionContext) {
	localctx = NewExpressionContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 8, SpecGrammarParserRULE_expression)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(183)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 5, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(176)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(177)
			p.Expression()
		}
		{
			p.SetState(178)
			p.Match(SpecGrammarParserRPAREN)
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(180)
			p.primary(0)
		}

	case 3:
		p.EnterOuterAlt(localctx, 3)
		{
			p.SetState(181)
			p.Unary()
		}

	case 4:
		p.EnterOuterAlt(localctx, 4)
		{
			p.SetState(182)
			p.binary(0)
		}

	}

	return localctx
}

// IPrimaryContext is an interface to support dynamic dispatch.
type IPrimaryContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsPrimaryContext differentiates from other interfaces.
	IsPrimaryContext()
}

type PrimaryContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyPrimaryContext() *PrimaryContext {
	var p = new(PrimaryContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_primary
	return p
}

func (*PrimaryContext) IsPrimaryContext() {}

func NewPrimaryContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *PrimaryContext {
	var p = new(PrimaryContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_primary

	return p
}

func (s *PrimaryContext) GetParser() antlr.Parser { return s.parser }

func (s *PrimaryContext) Operand() IOperandContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IOperandContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IOperandContext)
}

func (s *PrimaryContext) Primary() IPrimaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPrimaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPrimaryContext)
}

func (s *PrimaryContext) Dotnotation() IDotnotationContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IDotnotationContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IDotnotationContext)
}

func (s *PrimaryContext) Squarebracket() ISquarebracketContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ISquarebracketContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ISquarebracketContext)
}

func (s *PrimaryContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *PrimaryContext) ExpressionList() IExpressionListContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionListContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionListContext)
}

func (s *PrimaryContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *PrimaryContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *PrimaryContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *PrimaryContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterPrimary(s)
	}
}

func (s *PrimaryContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitPrimary(s)
	}
}

func (s *PrimaryContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitPrimary(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Primary() (localctx IPrimaryContext) {
	return p.primary(0)
}

func (p *SpecGrammarParser) primary(_p int) (localctx IPrimaryContext) {
	var _parentctx antlr.ParserRuleContext = p.GetParserRuleContext()
	_parentState := p.GetState()
	localctx = NewPrimaryContext(p, p.GetParserRuleContext(), _parentState)
	var _prevctx IPrimaryContext = localctx
	var _ antlr.ParserRuleContext = _prevctx // TODO: To prevent unused variable warning.
	_startState := 10
	p.EnterRecursionRule(localctx, 10, SpecGrammarParserRULE_primary, _p)

	defer func() {
		p.UnrollRecursionContexts(_parentctx)
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	var _alt int

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(186)
		p.Operand()
	}

	p.GetParserRuleContext().SetStop(p.GetTokenStream().LT(-1))
	p.SetState(203)
	p.GetErrorHandler().Sync(p)
	_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 8, p.GetParserRuleContext())

	for _alt != 2 && _alt != antlr.ATNInvalidAltNumber {
		if _alt == 1 {
			if p.GetParseListeners() != nil {
				p.TriggerExitRuleEvent()
			}
			_prevctx = localctx
			p.SetState(201)
			p.GetErrorHandler().Sync(p)
			switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 7, p.GetParserRuleContext()) {
			case 1:
				localctx = NewPrimaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_primary)
				p.SetState(188)

				if !(p.Precpred(p.GetParserRuleContext(), 3)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 3)", ""))
				}
				p.SetState(191)
				p.GetErrorHandler().Sync(p)

				switch p.GetTokenStream().LA(1) {
				case SpecGrammarParserDOT:
					{
						p.SetState(189)
						p.Dotnotation()
					}

				case SpecGrammarParserLSB:
					{
						p.SetState(190)
						p.Squarebracket()
					}

				default:
					panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
				}

			case 2:
				localctx = NewPrimaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_primary)
				p.SetState(193)

				if !(p.Precpred(p.GetParserRuleContext(), 2)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 2)", ""))
				}
				{
					p.SetState(194)
					p.Match(SpecGrammarParserLPAREN)
				}
				{
					p.SetState(195)
					p.ExpressionList()
				}
				{
					p.SetState(196)
					p.Match(SpecGrammarParserRPAREN)
				}

			case 3:
				localctx = NewPrimaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_primary)
				p.SetState(198)

				if !(p.Precpred(p.GetParserRuleContext(), 1)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 1)", ""))
				}
				{
					p.SetState(199)
					p.Match(SpecGrammarParserLPAREN)
				}
				{
					p.SetState(200)
					p.Match(SpecGrammarParserRPAREN)
				}

			}

		}
		p.SetState(205)
		p.GetErrorHandler().Sync(p)
		_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 8, p.GetParserRuleContext())
	}

	return localctx
}

// IUnaryContext is an interface to support dynamic dispatch.
type IUnaryContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetKind returns the kind token.
	GetKind() antlr.Token

	// SetKind sets the kind token.
	SetKind(antlr.Token)

	// IsUnaryContext differentiates from other interfaces.
	IsUnaryContext()
}

type UnaryContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
	kind   antlr.Token
}

func NewEmptyUnaryContext() *UnaryContext {
	var p = new(UnaryContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_unary
	return p
}

func (*UnaryContext) IsUnaryContext() {}

func NewUnaryContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *UnaryContext {
	var p = new(UnaryContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_unary

	return p
}

func (s *UnaryContext) GetParser() antlr.Parser { return s.parser }

func (s *UnaryContext) GetKind() antlr.Token { return s.kind }

func (s *UnaryContext) SetKind(v antlr.Token) { s.kind = v }

func (s *UnaryContext) Primary() IPrimaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPrimaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPrimaryContext)
}

func (s *UnaryContext) Unary() IUnaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IUnaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IUnaryContext)
}

func (s *UnaryContext) PLUS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserPLUS, 0)
}

func (s *UnaryContext) MINUS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserMINUS, 0)
}

func (s *UnaryContext) NOT() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserNOT, 0)
}

func (s *UnaryContext) STAR() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserSTAR, 0)
}

func (s *UnaryContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *UnaryContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *UnaryContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterUnary(s)
	}
}

func (s *UnaryContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitUnary(s)
	}
}

func (s *UnaryContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitUnary(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Unary() (localctx IUnaryContext) {
	localctx = NewUnaryContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 12, SpecGrammarParserRULE_unary)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(209)
	p.GetErrorHandler().Sync(p)

	switch p.GetTokenStream().LA(1) {
	case SpecGrammarParserOLD, SpecGrammarParserACCESS, SpecGrammarParserIDENTIFIER, SpecGrammarParserINTEGER, SpecGrammarParserLPAREN, SpecGrammarParserLSB:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(206)
			p.primary(0)
		}

	case SpecGrammarParserNOT, SpecGrammarParserPLUS, SpecGrammarParserMINUS, SpecGrammarParserSTAR:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(207)

			var _lt = p.GetTokenStream().LT(1)

			localctx.(*UnaryContext).kind = _lt

			_la = p.GetTokenStream().LA(1)

			if !(((_la-24)&-(0x1f+1)) == 0 && ((1<<uint((_la-24)))&((1<<(SpecGrammarParserNOT-24))|(1<<(SpecGrammarParserPLUS-24))|(1<<(SpecGrammarParserMINUS-24))|(1<<(SpecGrammarParserSTAR-24)))) != 0) {
				var _ri = p.GetErrorHandler().RecoverInline(p)

				localctx.(*UnaryContext).kind = _ri
			} else {
				p.GetErrorHandler().ReportMatch(p)
				p.Consume()
			}
		}
		{
			p.SetState(208)
			p.Unary()
		}

	default:
		panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
	}

	return localctx
}

// IBinaryContext is an interface to support dynamic dispatch.
type IBinaryContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetKind returns the kind token.
	GetKind() antlr.Token

	// SetKind sets the kind token.
	SetKind(antlr.Token)

	// IsBinaryContext differentiates from other interfaces.
	IsBinaryContext()
}

type BinaryContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
	kind   antlr.Token
}

func NewEmptyBinaryContext() *BinaryContext {
	var p = new(BinaryContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_binary
	return p
}

func (*BinaryContext) IsBinaryContext() {}

func NewBinaryContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *BinaryContext {
	var p = new(BinaryContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_binary

	return p
}

func (s *BinaryContext) GetParser() antlr.Parser { return s.parser }

func (s *BinaryContext) GetKind() antlr.Token { return s.kind }

func (s *BinaryContext) SetKind(v antlr.Token) { s.kind = v }

func (s *BinaryContext) Unary() IUnaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IUnaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IUnaryContext)
}

func (s *BinaryContext) AllBinary() []IBinaryContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IBinaryContext)(nil)).Elem())
	var tst = make([]IBinaryContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IBinaryContext)
		}
	}

	return tst
}

func (s *BinaryContext) Binary(i int) IBinaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IBinaryContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IBinaryContext)
}

func (s *BinaryContext) DIV() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserDIV, 0)
}

func (s *BinaryContext) MOD() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserMOD, 0)
}

func (s *BinaryContext) STAR() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserSTAR, 0)
}

func (s *BinaryContext) PLUS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserPLUS, 0)
}

func (s *BinaryContext) MINUS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserMINUS, 0)
}

func (s *BinaryContext) LEQ() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLEQ, 0)
}

func (s *BinaryContext) GEQ() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserGEQ, 0)
}

func (s *BinaryContext) GREAT() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserGREAT, 0)
}

func (s *BinaryContext) LESS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLESS, 0)
}

func (s *BinaryContext) EQ() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserEQ, 0)
}

func (s *BinaryContext) NEQ() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserNEQ, 0)
}

func (s *BinaryContext) AND() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserAND, 0)
}

func (s *BinaryContext) OR() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserOR, 0)
}

func (s *BinaryContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *BinaryContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *BinaryContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterBinary(s)
	}
}

func (s *BinaryContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitBinary(s)
	}
}

func (s *BinaryContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitBinary(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Binary() (localctx IBinaryContext) {
	return p.binary(0)
}

func (p *SpecGrammarParser) binary(_p int) (localctx IBinaryContext) {
	var _parentctx antlr.ParserRuleContext = p.GetParserRuleContext()
	_parentState := p.GetState()
	localctx = NewBinaryContext(p, p.GetParserRuleContext(), _parentState)
	var _prevctx IBinaryContext = localctx
	var _ antlr.ParserRuleContext = _prevctx // TODO: To prevent unused variable warning.
	_startState := 14
	p.EnterRecursionRule(localctx, 14, SpecGrammarParserRULE_binary, _p)
	var _la int

	defer func() {
		p.UnrollRecursionContexts(_parentctx)
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	var _alt int

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(212)
		p.Unary()
	}

	p.GetParserRuleContext().SetStop(p.GetTokenStream().LT(-1))
	p.SetState(234)
	p.GetErrorHandler().Sync(p)
	_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 11, p.GetParserRuleContext())

	for _alt != 2 && _alt != antlr.ATNInvalidAltNumber {
		if _alt == 1 {
			if p.GetParseListeners() != nil {
				p.TriggerExitRuleEvent()
			}
			_prevctx = localctx
			p.SetState(232)
			p.GetErrorHandler().Sync(p)
			switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 10, p.GetParserRuleContext()) {
			case 1:
				localctx = NewBinaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_binary)
				p.SetState(214)

				if !(p.Precpred(p.GetParserRuleContext(), 7)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 7)", ""))
				}
				{
					p.SetState(215)

					var _lt = p.GetTokenStream().LT(1)

					localctx.(*BinaryContext).kind = _lt

					_la = p.GetTokenStream().LA(1)

					if !(((_la-34)&-(0x1f+1)) == 0 && ((1<<uint((_la-34)))&((1<<(SpecGrammarParserDIV-34))|(1<<(SpecGrammarParserMOD-34))|(1<<(SpecGrammarParserSTAR-34)))) != 0) {
						var _ri = p.GetErrorHandler().RecoverInline(p)

						localctx.(*BinaryContext).kind = _ri
					} else {
						p.GetErrorHandler().ReportMatch(p)
						p.Consume()
					}
				}
				{
					p.SetState(216)
					p.binary(8)
				}

			case 2:
				localctx = NewBinaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_binary)
				p.SetState(217)

				if !(p.Precpred(p.GetParserRuleContext(), 6)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 6)", ""))
				}
				{
					p.SetState(218)

					var _lt = p.GetTokenStream().LT(1)

					localctx.(*BinaryContext).kind = _lt

					_la = p.GetTokenStream().LA(1)

					if !(_la == SpecGrammarParserPLUS || _la == SpecGrammarParserMINUS) {
						var _ri = p.GetErrorHandler().RecoverInline(p)

						localctx.(*BinaryContext).kind = _ri
					} else {
						p.GetErrorHandler().ReportMatch(p)
						p.Consume()
					}
				}
				{
					p.SetState(219)
					p.binary(7)
				}

			case 3:
				localctx = NewBinaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_binary)
				p.SetState(220)

				if !(p.Precpred(p.GetParserRuleContext(), 5)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 5)", ""))
				}
				{
					p.SetState(221)

					var _lt = p.GetTokenStream().LT(1)

					localctx.(*BinaryContext).kind = _lt

					_la = p.GetTokenStream().LA(1)

					if !(((_la-30)&-(0x1f+1)) == 0 && ((1<<uint((_la-30)))&((1<<(SpecGrammarParserLESS-30))|(1<<(SpecGrammarParserGREAT-30))|(1<<(SpecGrammarParserLEQ-30))|(1<<(SpecGrammarParserGEQ-30)))) != 0) {
						var _ri = p.GetErrorHandler().RecoverInline(p)

						localctx.(*BinaryContext).kind = _ri
					} else {
						p.GetErrorHandler().ReportMatch(p)
						p.Consume()
					}
				}
				{
					p.SetState(222)
					p.binary(6)
				}

			case 4:
				localctx = NewBinaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_binary)
				p.SetState(223)

				if !(p.Precpred(p.GetParserRuleContext(), 4)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 4)", ""))
				}
				{
					p.SetState(224)

					var _lt = p.GetTokenStream().LT(1)

					localctx.(*BinaryContext).kind = _lt

					_la = p.GetTokenStream().LA(1)

					if !(_la == SpecGrammarParserEQ || _la == SpecGrammarParserNEQ) {
						var _ri = p.GetErrorHandler().RecoverInline(p)

						localctx.(*BinaryContext).kind = _ri
					} else {
						p.GetErrorHandler().ReportMatch(p)
						p.Consume()
					}
				}
				{
					p.SetState(225)
					p.binary(5)
				}

			case 5:
				localctx = NewBinaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_binary)
				p.SetState(226)

				if !(p.Precpred(p.GetParserRuleContext(), 3)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 3)", ""))
				}
				{
					p.SetState(227)

					var _m = p.Match(SpecGrammarParserAND)

					localctx.(*BinaryContext).kind = _m
				}
				{
					p.SetState(228)
					p.binary(4)
				}

			case 6:
				localctx = NewBinaryContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_binary)
				p.SetState(229)

				if !(p.Precpred(p.GetParserRuleContext(), 2)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 2)", ""))
				}
				{
					p.SetState(230)

					var _m = p.Match(SpecGrammarParserOR)

					localctx.(*BinaryContext).kind = _m
				}
				{
					p.SetState(231)
					p.binary(3)
				}

			}

		}
		p.SetState(236)
		p.GetErrorHandler().Sync(p)
		_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 11, p.GetParserRuleContext())
	}

	return localctx
}

// IOperandContext is an interface to support dynamic dispatch.
type IOperandContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsOperandContext differentiates from other interfaces.
	IsOperandContext()
}

type OperandContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyOperandContext() *OperandContext {
	var p = new(OperandContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_operand
	return p
}

func (*OperandContext) IsOperandContext() {}

func NewOperandContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *OperandContext {
	var p = new(OperandContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_operand

	return p
}

func (s *OperandContext) GetParser() antlr.Parser { return s.parser }

func (s *OperandContext) Literal() ILiteralContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ILiteralContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ILiteralContext)
}

func (s *OperandContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *OperandContext) Old() IOldContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IOldContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IOldContext)
}

func (s *OperandContext) AccessPermission() IAccessPermissionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IAccessPermissionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IAccessPermissionContext)
}

func (s *OperandContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *OperandContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *OperandContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *OperandContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *OperandContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *OperandContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterOperand(s)
	}
}

func (s *OperandContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitOperand(s)
	}
}

func (s *OperandContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitOperand(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Operand() (localctx IOperandContext) {
	localctx = NewOperandContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 16, SpecGrammarParserRULE_operand)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(245)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 12, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(237)
			p.Literal()
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(238)
			p.Identifier()
		}

	case 3:
		p.EnterOuterAlt(localctx, 3)
		{
			p.SetState(239)
			p.Old()
		}

	case 4:
		p.EnterOuterAlt(localctx, 4)
		{
			p.SetState(240)
			p.AccessPermission()
		}

	case 5:
		p.EnterOuterAlt(localctx, 5)
		{
			p.SetState(241)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(242)
			p.Expression()
		}
		{
			p.SetState(243)
			p.Match(SpecGrammarParserRPAREN)
		}

	}

	return localctx
}

// ILiteralContext is an interface to support dynamic dispatch.
type ILiteralContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsLiteralContext differentiates from other interfaces.
	IsLiteralContext()
}

type LiteralContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyLiteralContext() *LiteralContext {
	var p = new(LiteralContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_literal
	return p
}

func (*LiteralContext) IsLiteralContext() {}

func NewLiteralContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *LiteralContext {
	var p = new(LiteralContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_literal

	return p
}

func (s *LiteralContext) GetParser() antlr.Parser { return s.parser }

func (s *LiteralContext) Integer() IIntegerContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIntegerContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIntegerContext)
}

func (s *LiteralContext) ArrayLit() IArrayLitContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IArrayLitContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IArrayLitContext)
}

func (s *LiteralContext) StructLit() IStructLitContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IStructLitContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IStructLitContext)
}

func (s *LiteralContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *LiteralContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *LiteralContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterLiteral(s)
	}
}

func (s *LiteralContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitLiteral(s)
	}
}

func (s *LiteralContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitLiteral(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Literal() (localctx ILiteralContext) {
	localctx = NewLiteralContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 18, SpecGrammarParserRULE_literal)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(250)
	p.GetErrorHandler().Sync(p)

	switch p.GetTokenStream().LA(1) {
	case SpecGrammarParserINTEGER:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(247)
			p.Integer()
		}

	case SpecGrammarParserLSB:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(248)
			p.ArrayLit()
		}

	case SpecGrammarParserIDENTIFIER:
		p.EnterOuterAlt(localctx, 3)
		{
			p.SetState(249)
			p.StructLit()
		}

	default:
		panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
	}

	return localctx
}

// IIntegerContext is an interface to support dynamic dispatch.
type IIntegerContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetKind returns the kind token.
	GetKind() antlr.Token

	// SetKind sets the kind token.
	SetKind(antlr.Token)

	// IsIntegerContext differentiates from other interfaces.
	IsIntegerContext()
}

type IntegerContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
	kind   antlr.Token
}

func NewEmptyIntegerContext() *IntegerContext {
	var p = new(IntegerContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_integer
	return p
}

func (*IntegerContext) IsIntegerContext() {}

func NewIntegerContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *IntegerContext {
	var p = new(IntegerContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_integer

	return p
}

func (s *IntegerContext) GetParser() antlr.Parser { return s.parser }

func (s *IntegerContext) GetKind() antlr.Token { return s.kind }

func (s *IntegerContext) SetKind(v antlr.Token) { s.kind = v }

func (s *IntegerContext) INTEGER() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserINTEGER, 0)
}

func (s *IntegerContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *IntegerContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *IntegerContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterInteger(s)
	}
}

func (s *IntegerContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitInteger(s)
	}
}

func (s *IntegerContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitInteger(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Integer() (localctx IIntegerContext) {
	localctx = NewIntegerContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 20, SpecGrammarParserRULE_integer)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(252)

		var _m = p.Match(SpecGrammarParserINTEGER)

		localctx.(*IntegerContext).kind = _m
	}

	return localctx
}

// IIdentifierContext is an interface to support dynamic dispatch.
type IIdentifierContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsIdentifierContext differentiates from other interfaces.
	IsIdentifierContext()
}

type IdentifierContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyIdentifierContext() *IdentifierContext {
	var p = new(IdentifierContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_identifier
	return p
}

func (*IdentifierContext) IsIdentifierContext() {}

func NewIdentifierContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *IdentifierContext {
	var p = new(IdentifierContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_identifier

	return p
}

func (s *IdentifierContext) GetParser() antlr.Parser { return s.parser }

func (s *IdentifierContext) IDENTIFIER() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserIDENTIFIER, 0)
}

func (s *IdentifierContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *IdentifierContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *IdentifierContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterIdentifier(s)
	}
}

func (s *IdentifierContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitIdentifier(s)
	}
}

func (s *IdentifierContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitIdentifier(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Identifier() (localctx IIdentifierContext) {
	localctx = NewIdentifierContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 22, SpecGrammarParserRULE_identifier)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(254)
		p.Match(SpecGrammarParserIDENTIFIER)
	}

	return localctx
}

// ISquarebracketContext is an interface to support dynamic dispatch.
type ISquarebracketContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsSquarebracketContext differentiates from other interfaces.
	IsSquarebracketContext()
}

type SquarebracketContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptySquarebracketContext() *SquarebracketContext {
	var p = new(SquarebracketContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_squarebracket
	return p
}

func (*SquarebracketContext) IsSquarebracketContext() {}

func NewSquarebracketContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *SquarebracketContext {
	var p = new(SquarebracketContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_squarebracket

	return p
}

func (s *SquarebracketContext) GetParser() antlr.Parser { return s.parser }

func (s *SquarebracketContext) LSB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLSB, 0)
}

func (s *SquarebracketContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *SquarebracketContext) RSB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRSB, 0)
}

func (s *SquarebracketContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *SquarebracketContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *SquarebracketContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterSquarebracket(s)
	}
}

func (s *SquarebracketContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitSquarebracket(s)
	}
}

func (s *SquarebracketContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitSquarebracket(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Squarebracket() (localctx ISquarebracketContext) {
	localctx = NewSquarebracketContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 24, SpecGrammarParserRULE_squarebracket)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(256)
		p.Match(SpecGrammarParserLSB)
	}
	{
		p.SetState(257)
		p.Expression()
	}
	{
		p.SetState(258)
		p.Match(SpecGrammarParserRSB)
	}

	return localctx
}

// IDotnotationContext is an interface to support dynamic dispatch.
type IDotnotationContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsDotnotationContext differentiates from other interfaces.
	IsDotnotationContext()
}

type DotnotationContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyDotnotationContext() *DotnotationContext {
	var p = new(DotnotationContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_dotnotation
	return p
}

func (*DotnotationContext) IsDotnotationContext() {}

func NewDotnotationContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *DotnotationContext {
	var p = new(DotnotationContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_dotnotation

	return p
}

func (s *DotnotationContext) GetParser() antlr.Parser { return s.parser }

func (s *DotnotationContext) DOT() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserDOT, 0)
}

func (s *DotnotationContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *DotnotationContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *DotnotationContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *DotnotationContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterDotnotation(s)
	}
}

func (s *DotnotationContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitDotnotation(s)
	}
}

func (s *DotnotationContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitDotnotation(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Dotnotation() (localctx IDotnotationContext) {
	localctx = NewDotnotationContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 26, SpecGrammarParserRULE_dotnotation)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(260)
		p.Match(SpecGrammarParserDOT)
	}
	{
		p.SetState(261)
		p.Identifier()
	}

	return localctx
}

// IArrayLitContext is an interface to support dynamic dispatch.
type IArrayLitContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsArrayLitContext differentiates from other interfaces.
	IsArrayLitContext()
}

type ArrayLitContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyArrayLitContext() *ArrayLitContext {
	var p = new(ArrayLitContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_arrayLit
	return p
}

func (*ArrayLitContext) IsArrayLitContext() {}

func NewArrayLitContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ArrayLitContext {
	var p = new(ArrayLitContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_arrayLit

	return p
}

func (s *ArrayLitContext) GetParser() antlr.Parser { return s.parser }

func (s *ArrayLitContext) ArrayType() IArrayTypeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IArrayTypeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IArrayTypeContext)
}

func (s *ArrayLitContext) LiteralValue() ILiteralValueContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ILiteralValueContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ILiteralValueContext)
}

func (s *ArrayLitContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ArrayLitContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ArrayLitContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterArrayLit(s)
	}
}

func (s *ArrayLitContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitArrayLit(s)
	}
}

func (s *ArrayLitContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitArrayLit(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ArrayLit() (localctx IArrayLitContext) {
	localctx = NewArrayLitContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 28, SpecGrammarParserRULE_arrayLit)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(263)
		p.ArrayType()
	}
	{
		p.SetState(264)
		p.LiteralValue()
	}

	return localctx
}

// IStructLitContext is an interface to support dynamic dispatch.
type IStructLitContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsStructLitContext differentiates from other interfaces.
	IsStructLitContext()
}

type StructLitContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyStructLitContext() *StructLitContext {
	var p = new(StructLitContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_structLit
	return p
}

func (*StructLitContext) IsStructLitContext() {}

func NewStructLitContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *StructLitContext {
	var p = new(StructLitContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_structLit

	return p
}

func (s *StructLitContext) GetParser() antlr.Parser { return s.parser }

func (s *StructLitContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *StructLitContext) LiteralValue() ILiteralValueContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ILiteralValueContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ILiteralValueContext)
}

func (s *StructLitContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *StructLitContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *StructLitContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterStructLit(s)
	}
}

func (s *StructLitContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitStructLit(s)
	}
}

func (s *StructLitContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitStructLit(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) StructLit() (localctx IStructLitContext) {
	localctx = NewStructLitContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 30, SpecGrammarParserRULE_structLit)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(266)
		p.Identifier()
	}
	{
		p.SetState(267)
		p.LiteralValue()
	}

	return localctx
}

// ILiteralValueContext is an interface to support dynamic dispatch.
type ILiteralValueContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsLiteralValueContext differentiates from other interfaces.
	IsLiteralValueContext()
}

type LiteralValueContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyLiteralValueContext() *LiteralValueContext {
	var p = new(LiteralValueContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_literalValue
	return p
}

func (*LiteralValueContext) IsLiteralValueContext() {}

func NewLiteralValueContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *LiteralValueContext {
	var p = new(LiteralValueContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_literalValue

	return p
}

func (s *LiteralValueContext) GetParser() antlr.Parser { return s.parser }

func (s *LiteralValueContext) LCB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLCB, 0)
}

func (s *LiteralValueContext) RCB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRCB, 0)
}

func (s *LiteralValueContext) ElementList() IElementListContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IElementListContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IElementListContext)
}

func (s *LiteralValueContext) COMMA() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, 0)
}

func (s *LiteralValueContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *LiteralValueContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *LiteralValueContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterLiteralValue(s)
	}
}

func (s *LiteralValueContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitLiteralValue(s)
	}
}

func (s *LiteralValueContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitLiteralValue(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) LiteralValue() (localctx ILiteralValueContext) {
	localctx = NewLiteralValueContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 32, SpecGrammarParserRULE_literalValue)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(269)
		p.Match(SpecGrammarParserLCB)
	}
	p.SetState(274)
	p.GetErrorHandler().Sync(p)
	_la = p.GetTokenStream().LA(1)

	if (((_la)&-(0x1f+1)) == 0 && ((1<<uint(_la))&((1<<SpecGrammarParserOLD)|(1<<SpecGrammarParserACCESS)|(1<<SpecGrammarParserIDENTIFIER)|(1<<SpecGrammarParserINTEGER)|(1<<SpecGrammarParserLPAREN)|(1<<SpecGrammarParserLSB)|(1<<SpecGrammarParserLCB)|(1<<SpecGrammarParserNOT))) != 0) || (((_la-39)&-(0x1f+1)) == 0 && ((1<<uint((_la-39)))&((1<<(SpecGrammarParserPLUS-39))|(1<<(SpecGrammarParserMINUS-39))|(1<<(SpecGrammarParserSTAR-39)))) != 0) {
		{
			p.SetState(270)
			p.ElementList()
		}
		p.SetState(272)
		p.GetErrorHandler().Sync(p)
		_la = p.GetTokenStream().LA(1)

		if _la == SpecGrammarParserCOMMA {
			{
				p.SetState(271)
				p.Match(SpecGrammarParserCOMMA)
			}

		}

	}
	{
		p.SetState(276)
		p.Match(SpecGrammarParserRCB)
	}

	return localctx
}

// IElementListContext is an interface to support dynamic dispatch.
type IElementListContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsElementListContext differentiates from other interfaces.
	IsElementListContext()
}

type ElementListContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyElementListContext() *ElementListContext {
	var p = new(ElementListContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_elementList
	return p
}

func (*ElementListContext) IsElementListContext() {}

func NewElementListContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ElementListContext {
	var p = new(ElementListContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_elementList

	return p
}

func (s *ElementListContext) GetParser() antlr.Parser { return s.parser }

func (s *ElementListContext) AllKeyedElement() []IKeyedElementContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IKeyedElementContext)(nil)).Elem())
	var tst = make([]IKeyedElementContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IKeyedElementContext)
		}
	}

	return tst
}

func (s *ElementListContext) KeyedElement(i int) IKeyedElementContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IKeyedElementContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IKeyedElementContext)
}

func (s *ElementListContext) AllCOMMA() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserCOMMA)
}

func (s *ElementListContext) COMMA(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, i)
}

func (s *ElementListContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ElementListContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ElementListContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterElementList(s)
	}
}

func (s *ElementListContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitElementList(s)
	}
}

func (s *ElementListContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitElementList(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ElementList() (localctx IElementListContext) {
	localctx = NewElementListContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 34, SpecGrammarParserRULE_elementList)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	var _alt int

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(278)
		p.KeyedElement()
	}
	p.SetState(283)
	p.GetErrorHandler().Sync(p)
	_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 16, p.GetParserRuleContext())

	for _alt != 2 && _alt != antlr.ATNInvalidAltNumber {
		if _alt == 1 {
			{
				p.SetState(279)
				p.Match(SpecGrammarParserCOMMA)
			}
			{
				p.SetState(280)
				p.KeyedElement()
			}

		}
		p.SetState(285)
		p.GetErrorHandler().Sync(p)
		_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 16, p.GetParserRuleContext())
	}

	return localctx
}

// IKeyedElementContext is an interface to support dynamic dispatch.
type IKeyedElementContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsKeyedElementContext differentiates from other interfaces.
	IsKeyedElementContext()
}

type KeyedElementContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyKeyedElementContext() *KeyedElementContext {
	var p = new(KeyedElementContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_keyedElement
	return p
}

func (*KeyedElementContext) IsKeyedElementContext() {}

func NewKeyedElementContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *KeyedElementContext {
	var p = new(KeyedElementContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_keyedElement

	return p
}

func (s *KeyedElementContext) GetParser() antlr.Parser { return s.parser }

func (s *KeyedElementContext) Element() IElementContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IElementContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IElementContext)
}

func (s *KeyedElementContext) Key() IKeyContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IKeyContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IKeyContext)
}

func (s *KeyedElementContext) COLON() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOLON, 0)
}

func (s *KeyedElementContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *KeyedElementContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *KeyedElementContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterKeyedElement(s)
	}
}

func (s *KeyedElementContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitKeyedElement(s)
	}
}

func (s *KeyedElementContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitKeyedElement(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) KeyedElement() (localctx IKeyedElementContext) {
	localctx = NewKeyedElementContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 36, SpecGrammarParserRULE_keyedElement)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	p.SetState(289)
	p.GetErrorHandler().Sync(p)

	if p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 17, p.GetParserRuleContext()) == 1 {
		{
			p.SetState(286)
			p.Key()
		}
		{
			p.SetState(287)
			p.Match(SpecGrammarParserCOLON)
		}

	}
	{
		p.SetState(291)
		p.Element()
	}

	return localctx
}

// IKeyContext is an interface to support dynamic dispatch.
type IKeyContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsKeyContext differentiates from other interfaces.
	IsKeyContext()
}

type KeyContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyKeyContext() *KeyContext {
	var p = new(KeyContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_key
	return p
}

func (*KeyContext) IsKeyContext() {}

func NewKeyContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *KeyContext {
	var p = new(KeyContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_key

	return p
}

func (s *KeyContext) GetParser() antlr.Parser { return s.parser }

func (s *KeyContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *KeyContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *KeyContext) LiteralValue() ILiteralValueContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ILiteralValueContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ILiteralValueContext)
}

func (s *KeyContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *KeyContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *KeyContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterKey(s)
	}
}

func (s *KeyContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitKey(s)
	}
}

func (s *KeyContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitKey(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Key() (localctx IKeyContext) {
	localctx = NewKeyContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 38, SpecGrammarParserRULE_key)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(296)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 18, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(293)
			p.Identifier()
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(294)
			p.Expression()
		}

	case 3:
		p.EnterOuterAlt(localctx, 3)
		{
			p.SetState(295)
			p.LiteralValue()
		}

	}

	return localctx
}

// IElementContext is an interface to support dynamic dispatch.
type IElementContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsElementContext differentiates from other interfaces.
	IsElementContext()
}

type ElementContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyElementContext() *ElementContext {
	var p = new(ElementContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_element
	return p
}

func (*ElementContext) IsElementContext() {}

func NewElementContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ElementContext {
	var p = new(ElementContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_element

	return p
}

func (s *ElementContext) GetParser() antlr.Parser { return s.parser }

func (s *ElementContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *ElementContext) LiteralValue() ILiteralValueContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ILiteralValueContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ILiteralValueContext)
}

func (s *ElementContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ElementContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ElementContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterElement(s)
	}
}

func (s *ElementContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitElement(s)
	}
}

func (s *ElementContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitElement(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Element() (localctx IElementContext) {
	localctx = NewElementContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 40, SpecGrammarParserRULE_element)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(300)
	p.GetErrorHandler().Sync(p)

	switch p.GetTokenStream().LA(1) {
	case SpecGrammarParserOLD, SpecGrammarParserACCESS, SpecGrammarParserIDENTIFIER, SpecGrammarParserINTEGER, SpecGrammarParserLPAREN, SpecGrammarParserLSB, SpecGrammarParserNOT, SpecGrammarParserPLUS, SpecGrammarParserMINUS, SpecGrammarParserSTAR:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(298)
			p.Expression()
		}

	case SpecGrammarParserLCB:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(299)
			p.LiteralValue()
		}

	default:
		panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
	}

	return localctx
}

// IArrayTypeContext is an interface to support dynamic dispatch.
type IArrayTypeContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsArrayTypeContext differentiates from other interfaces.
	IsArrayTypeContext()
}

type ArrayTypeContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyArrayTypeContext() *ArrayTypeContext {
	var p = new(ArrayTypeContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_arrayType
	return p
}

func (*ArrayTypeContext) IsArrayTypeContext() {}

func NewArrayTypeContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ArrayTypeContext {
	var p = new(ArrayTypeContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_arrayType

	return p
}

func (s *ArrayTypeContext) GetParser() antlr.Parser { return s.parser }

func (s *ArrayTypeContext) LSB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLSB, 0)
}

func (s *ArrayTypeContext) ArrayLength() IArrayLengthContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IArrayLengthContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IArrayLengthContext)
}

func (s *ArrayTypeContext) RSB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRSB, 0)
}

func (s *ArrayTypeContext) ElementType() IElementTypeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IElementTypeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IElementTypeContext)
}

func (s *ArrayTypeContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ArrayTypeContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ArrayTypeContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterArrayType(s)
	}
}

func (s *ArrayTypeContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitArrayType(s)
	}
}

func (s *ArrayTypeContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitArrayType(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ArrayType() (localctx IArrayTypeContext) {
	localctx = NewArrayTypeContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 42, SpecGrammarParserRULE_arrayType)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(310)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 20, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(302)
			p.Match(SpecGrammarParserLSB)
		}
		{
			p.SetState(303)
			p.ArrayLength()
		}
		{
			p.SetState(304)
			p.Match(SpecGrammarParserRSB)
		}
		{
			p.SetState(305)
			p.ElementType()
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(307)
			p.Match(SpecGrammarParserLSB)
		}
		{
			p.SetState(308)
			p.Match(SpecGrammarParserRSB)
		}
		{
			p.SetState(309)
			p.ElementType()
		}

	}

	return localctx
}

// IArrayLengthContext is an interface to support dynamic dispatch.
type IArrayLengthContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsArrayLengthContext differentiates from other interfaces.
	IsArrayLengthContext()
}

type ArrayLengthContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyArrayLengthContext() *ArrayLengthContext {
	var p = new(ArrayLengthContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_arrayLength
	return p
}

func (*ArrayLengthContext) IsArrayLengthContext() {}

func NewArrayLengthContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ArrayLengthContext {
	var p = new(ArrayLengthContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_arrayLength

	return p
}

func (s *ArrayLengthContext) GetParser() antlr.Parser { return s.parser }

func (s *ArrayLengthContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *ArrayLengthContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ArrayLengthContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ArrayLengthContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterArrayLength(s)
	}
}

func (s *ArrayLengthContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitArrayLength(s)
	}
}

func (s *ArrayLengthContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitArrayLength(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ArrayLength() (localctx IArrayLengthContext) {
	localctx = NewArrayLengthContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 44, SpecGrammarParserRULE_arrayLength)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(312)
		p.Expression()
	}

	return localctx
}

// IElementTypeContext is an interface to support dynamic dispatch.
type IElementTypeContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsElementTypeContext differentiates from other interfaces.
	IsElementTypeContext()
}

type ElementTypeContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyElementTypeContext() *ElementTypeContext {
	var p = new(ElementTypeContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_elementType
	return p
}

func (*ElementTypeContext) IsElementTypeContext() {}

func NewElementTypeContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ElementTypeContext {
	var p = new(ElementTypeContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_elementType

	return p
}

func (s *ElementTypeContext) GetParser() antlr.Parser { return s.parser }

func (s *ElementTypeContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *ElementTypeContext) TypeLit() ITypeLitContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*ITypeLitContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(ITypeLitContext)
}

func (s *ElementTypeContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ElementTypeContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ElementTypeContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterElementType(s)
	}
}

func (s *ElementTypeContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitElementType(s)
	}
}

func (s *ElementTypeContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitElementType(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ElementType() (localctx IElementTypeContext) {
	localctx = NewElementTypeContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 46, SpecGrammarParserRULE_elementType)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(316)
	p.GetErrorHandler().Sync(p)

	switch p.GetTokenStream().LA(1) {
	case SpecGrammarParserIDENTIFIER:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(314)
			p.Identifier()
		}

	case SpecGrammarParserLSB, SpecGrammarParserSTAR:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(315)
			p.TypeLit()
		}

	default:
		panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
	}

	return localctx
}

// ITypeLitContext is an interface to support dynamic dispatch.
type ITypeLitContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsTypeLitContext differentiates from other interfaces.
	IsTypeLitContext()
}

type TypeLitContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyTypeLitContext() *TypeLitContext {
	var p = new(TypeLitContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_typeLit
	return p
}

func (*TypeLitContext) IsTypeLitContext() {}

func NewTypeLitContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *TypeLitContext {
	var p = new(TypeLitContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_typeLit

	return p
}

func (s *TypeLitContext) GetParser() antlr.Parser { return s.parser }

func (s *TypeLitContext) ArrayType() IArrayTypeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IArrayTypeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IArrayTypeContext)
}

func (s *TypeLitContext) PointerType() IPointerTypeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPointerTypeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPointerTypeContext)
}

func (s *TypeLitContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *TypeLitContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *TypeLitContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterTypeLit(s)
	}
}

func (s *TypeLitContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitTypeLit(s)
	}
}

func (s *TypeLitContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitTypeLit(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) TypeLit() (localctx ITypeLitContext) {
	localctx = NewTypeLitContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 48, SpecGrammarParserRULE_typeLit)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(320)
	p.GetErrorHandler().Sync(p)

	switch p.GetTokenStream().LA(1) {
	case SpecGrammarParserLSB:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(318)
			p.ArrayType()
		}

	case SpecGrammarParserSTAR:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(319)
			p.PointerType()
		}

	default:
		panic(antlr.NewNoViableAltException(p, nil, nil, nil, nil, nil))
	}

	return localctx
}

// IPointerTypeContext is an interface to support dynamic dispatch.
type IPointerTypeContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsPointerTypeContext differentiates from other interfaces.
	IsPointerTypeContext()
}

type PointerTypeContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyPointerTypeContext() *PointerTypeContext {
	var p = new(PointerTypeContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_pointerType
	return p
}

func (*PointerTypeContext) IsPointerTypeContext() {}

func NewPointerTypeContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *PointerTypeContext {
	var p = new(PointerTypeContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_pointerType

	return p
}

func (s *PointerTypeContext) GetParser() antlr.Parser { return s.parser }

func (s *PointerTypeContext) STAR() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserSTAR, 0)
}

func (s *PointerTypeContext) ElementType() IElementTypeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IElementTypeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IElementTypeContext)
}

func (s *PointerTypeContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *PointerTypeContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *PointerTypeContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterPointerType(s)
	}
}

func (s *PointerTypeContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitPointerType(s)
	}
}

func (s *PointerTypeContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitPointerType(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) PointerType() (localctx IPointerTypeContext) {
	localctx = NewPointerTypeContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 50, SpecGrammarParserRULE_pointerType)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(322)
		p.Match(SpecGrammarParserSTAR)
	}
	{
		p.SetState(323)
		p.ElementType()
	}

	return localctx
}

// IPurityContext is an interface to support dynamic dispatch.
type IPurityContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsPurityContext differentiates from other interfaces.
	IsPurityContext()
}

type PurityContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyPurityContext() *PurityContext {
	var p = new(PurityContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_purity
	return p
}

func (*PurityContext) IsPurityContext() {}

func NewPurityContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *PurityContext {
	var p = new(PurityContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_purity

	return p
}

func (s *PurityContext) GetParser() antlr.Parser { return s.parser }

func (s *PurityContext) PURE() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserPURE, 0)
}

func (s *PurityContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *PurityContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *PurityContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterPurity(s)
	}
}

func (s *PurityContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitPurity(s)
	}
}

func (s *PurityContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitPurity(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Purity() (localctx IPurityContext) {
	localctx = NewPurityContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 52, SpecGrammarParserRULE_purity)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(325)
		p.Match(SpecGrammarParserPURE)
	}

	return localctx
}

// ISharedVarsNotationContext is an interface to support dynamic dispatch.
type ISharedVarsNotationContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsSharedVarsNotationContext differentiates from other interfaces.
	IsSharedVarsNotationContext()
}

type SharedVarsNotationContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptySharedVarsNotationContext() *SharedVarsNotationContext {
	var p = new(SharedVarsNotationContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_sharedVarsNotation
	return p
}

func (*SharedVarsNotationContext) IsSharedVarsNotationContext() {}

func NewSharedVarsNotationContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *SharedVarsNotationContext {
	var p = new(SharedVarsNotationContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_sharedVarsNotation

	return p
}

func (s *SharedVarsNotationContext) GetParser() antlr.Parser { return s.parser }

func (s *SharedVarsNotationContext) SHARED() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserSHARED, 0)
}

func (s *SharedVarsNotationContext) COLON() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOLON, 0)
}

func (s *SharedVarsNotationContext) IdentifierList() IIdentifierListContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierListContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierListContext)
}

func (s *SharedVarsNotationContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *SharedVarsNotationContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *SharedVarsNotationContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterSharedVarsNotation(s)
	}
}

func (s *SharedVarsNotationContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitSharedVarsNotation(s)
	}
}

func (s *SharedVarsNotationContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitSharedVarsNotation(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) SharedVarsNotation() (localctx ISharedVarsNotationContext) {
	localctx = NewSharedVarsNotationContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 54, SpecGrammarParserRULE_sharedVarsNotation)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(327)
		p.Match(SpecGrammarParserSHARED)
	}
	{
		p.SetState(328)
		p.Match(SpecGrammarParserCOLON)
	}
	{
		p.SetState(329)
		p.IdentifierList()
	}

	return localctx
}

// IExclusiveVarsNotationContext is an interface to support dynamic dispatch.
type IExclusiveVarsNotationContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsExclusiveVarsNotationContext differentiates from other interfaces.
	IsExclusiveVarsNotationContext()
}

type ExclusiveVarsNotationContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyExclusiveVarsNotationContext() *ExclusiveVarsNotationContext {
	var p = new(ExclusiveVarsNotationContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_exclusiveVarsNotation
	return p
}

func (*ExclusiveVarsNotationContext) IsExclusiveVarsNotationContext() {}

func NewExclusiveVarsNotationContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ExclusiveVarsNotationContext {
	var p = new(ExclusiveVarsNotationContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_exclusiveVarsNotation

	return p
}

func (s *ExclusiveVarsNotationContext) GetParser() antlr.Parser { return s.parser }

func (s *ExclusiveVarsNotationContext) EXCLUSIVE() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserEXCLUSIVE, 0)
}

func (s *ExclusiveVarsNotationContext) COLON() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOLON, 0)
}

func (s *ExclusiveVarsNotationContext) IdentifierList() IIdentifierListContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierListContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierListContext)
}

func (s *ExclusiveVarsNotationContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ExclusiveVarsNotationContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ExclusiveVarsNotationContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterExclusiveVarsNotation(s)
	}
}

func (s *ExclusiveVarsNotationContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitExclusiveVarsNotation(s)
	}
}

func (s *ExclusiveVarsNotationContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitExclusiveVarsNotation(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ExclusiveVarsNotation() (localctx IExclusiveVarsNotationContext) {
	localctx = NewExclusiveVarsNotationContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 56, SpecGrammarParserRULE_exclusiveVarsNotation)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(331)
		p.Match(SpecGrammarParserEXCLUSIVE)
	}
	{
		p.SetState(332)
		p.Match(SpecGrammarParserCOLON)
	}
	{
		p.SetState(333)
		p.IdentifierList()
	}

	return localctx
}

// IOldContext is an interface to support dynamic dispatch.
type IOldContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsOldContext differentiates from other interfaces.
	IsOldContext()
}

type OldContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyOldContext() *OldContext {
	var p = new(OldContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_old
	return p
}

func (*OldContext) IsOldContext() {}

func NewOldContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *OldContext {
	var p = new(OldContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_old

	return p
}

func (s *OldContext) GetParser() antlr.Parser { return s.parser }

func (s *OldContext) OLD() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserOLD, 0)
}

func (s *OldContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *OldContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *OldContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *OldContext) LSB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLSB, 0)
}

func (s *OldContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *OldContext) RSB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRSB, 0)
}

func (s *OldContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *OldContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *OldContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterOld(s)
	}
}

func (s *OldContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitOld(s)
	}
}

func (s *OldContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitOld(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Old() (localctx IOldContext) {
	localctx = NewOldContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 58, SpecGrammarParserRULE_old)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(348)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 23, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(335)
			p.Match(SpecGrammarParserOLD)
		}
		{
			p.SetState(336)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(337)
			p.Expression()
		}
		{
			p.SetState(338)
			p.Match(SpecGrammarParserRPAREN)
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(340)
			p.Match(SpecGrammarParserOLD)
		}
		{
			p.SetState(341)
			p.Match(SpecGrammarParserLSB)
		}
		{
			p.SetState(342)
			p.Identifier()
		}
		{
			p.SetState(343)
			p.Match(SpecGrammarParserRSB)
		}
		{
			p.SetState(344)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(345)
			p.Expression()
		}
		{
			p.SetState(346)
			p.Match(SpecGrammarParserRPAREN)
		}

	}

	return localctx
}

// ILabelContext is an interface to support dynamic dispatch.
type ILabelContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsLabelContext differentiates from other interfaces.
	IsLabelContext()
}

type LabelContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyLabelContext() *LabelContext {
	var p = new(LabelContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_label
	return p
}

func (*LabelContext) IsLabelContext() {}

func NewLabelContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *LabelContext {
	var p = new(LabelContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_label

	return p
}

func (s *LabelContext) GetParser() antlr.Parser { return s.parser }

func (s *LabelContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *LabelContext) COLON() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOLON, 0)
}

func (s *LabelContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *LabelContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *LabelContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterLabel(s)
	}
}

func (s *LabelContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitLabel(s)
	}
}

func (s *LabelContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitLabel(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Label() (localctx ILabelContext) {
	localctx = NewLabelContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 60, SpecGrammarParserRULE_label)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(350)
		p.Identifier()
	}
	{
		p.SetState(351)
		p.Match(SpecGrammarParserCOLON)
	}

	return localctx
}

// IVariableListContext is an interface to support dynamic dispatch.
type IVariableListContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsVariableListContext differentiates from other interfaces.
	IsVariableListContext()
}

type VariableListContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyVariableListContext() *VariableListContext {
	var p = new(VariableListContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_variableList
	return p
}

func (*VariableListContext) IsVariableListContext() {}

func NewVariableListContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *VariableListContext {
	var p = new(VariableListContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_variableList

	return p
}

func (s *VariableListContext) GetParser() antlr.Parser { return s.parser }

func (s *VariableListContext) AllVarTypeTuple() []IVarTypeTupleContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IVarTypeTupleContext)(nil)).Elem())
	var tst = make([]IVarTypeTupleContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IVarTypeTupleContext)
		}
	}

	return tst
}

func (s *VariableListContext) VarTypeTuple(i int) IVarTypeTupleContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IVarTypeTupleContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IVarTypeTupleContext)
}

func (s *VariableListContext) AllCOMMA() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserCOMMA)
}

func (s *VariableListContext) COMMA(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, i)
}

func (s *VariableListContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *VariableListContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *VariableListContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterVariableList(s)
	}
}

func (s *VariableListContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitVariableList(s)
	}
}

func (s *VariableListContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitVariableList(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) VariableList() (localctx IVariableListContext) {
	localctx = NewVariableListContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 62, SpecGrammarParserRULE_variableList)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	var _alt int

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(353)
		p.VarTypeTuple()
	}
	p.SetState(358)
	p.GetErrorHandler().Sync(p)
	_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 24, p.GetParserRuleContext())

	for _alt != 2 && _alt != antlr.ATNInvalidAltNumber {
		if _alt == 1 {
			{
				p.SetState(354)
				p.Match(SpecGrammarParserCOMMA)
			}
			{
				p.SetState(355)
				p.VarTypeTuple()
			}

		}
		p.SetState(360)
		p.GetErrorHandler().Sync(p)
		_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 24, p.GetParserRuleContext())
	}
	p.SetState(362)
	p.GetErrorHandler().Sync(p)
	_la = p.GetTokenStream().LA(1)

	if _la == SpecGrammarParserCOMMA {
		{
			p.SetState(361)
			p.Match(SpecGrammarParserCOMMA)
		}

	}

	return localctx
}

// IExpressionListContext is an interface to support dynamic dispatch.
type IExpressionListContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsExpressionListContext differentiates from other interfaces.
	IsExpressionListContext()
}

type ExpressionListContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyExpressionListContext() *ExpressionListContext {
	var p = new(ExpressionListContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_expressionList
	return p
}

func (*ExpressionListContext) IsExpressionListContext() {}

func NewExpressionListContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ExpressionListContext {
	var p = new(ExpressionListContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_expressionList

	return p
}

func (s *ExpressionListContext) GetParser() antlr.Parser { return s.parser }

func (s *ExpressionListContext) AllExpression() []IExpressionContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IExpressionContext)(nil)).Elem())
	var tst = make([]IExpressionContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IExpressionContext)
		}
	}

	return tst
}

func (s *ExpressionListContext) Expression(i int) IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *ExpressionListContext) AllCOMMA() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserCOMMA)
}

func (s *ExpressionListContext) COMMA(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, i)
}

func (s *ExpressionListContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ExpressionListContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ExpressionListContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterExpressionList(s)
	}
}

func (s *ExpressionListContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitExpressionList(s)
	}
}

func (s *ExpressionListContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitExpressionList(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) ExpressionList() (localctx IExpressionListContext) {
	localctx = NewExpressionListContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 64, SpecGrammarParserRULE_expressionList)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(364)
		p.Expression()
	}
	p.SetState(369)
	p.GetErrorHandler().Sync(p)
	_la = p.GetTokenStream().LA(1)

	for _la == SpecGrammarParserCOMMA {
		{
			p.SetState(365)
			p.Match(SpecGrammarParserCOMMA)
		}
		{
			p.SetState(366)
			p.Expression()
		}

		p.SetState(371)
		p.GetErrorHandler().Sync(p)
		_la = p.GetTokenStream().LA(1)
	}

	return localctx
}

// IIdentifierListContext is an interface to support dynamic dispatch.
type IIdentifierListContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsIdentifierListContext differentiates from other interfaces.
	IsIdentifierListContext()
}

type IdentifierListContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyIdentifierListContext() *IdentifierListContext {
	var p = new(IdentifierListContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_identifierList
	return p
}

func (*IdentifierListContext) IsIdentifierListContext() {}

func NewIdentifierListContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *IdentifierListContext {
	var p = new(IdentifierListContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_identifierList

	return p
}

func (s *IdentifierListContext) GetParser() antlr.Parser { return s.parser }

func (s *IdentifierListContext) AllIdentifier() []IIdentifierContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IIdentifierContext)(nil)).Elem())
	var tst = make([]IIdentifierContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IIdentifierContext)
		}
	}

	return tst
}

func (s *IdentifierListContext) Identifier(i int) IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *IdentifierListContext) AllCOMMA() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserCOMMA)
}

func (s *IdentifierListContext) COMMA(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, i)
}

func (s *IdentifierListContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *IdentifierListContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *IdentifierListContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterIdentifierList(s)
	}
}

func (s *IdentifierListContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitIdentifierList(s)
	}
}

func (s *IdentifierListContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitIdentifierList(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) IdentifierList() (localctx IIdentifierListContext) {
	localctx = NewIdentifierListContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 66, SpecGrammarParserRULE_identifierList)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(372)
		p.Identifier()
	}
	p.SetState(377)
	p.GetErrorHandler().Sync(p)
	_la = p.GetTokenStream().LA(1)

	for _la == SpecGrammarParserCOMMA {
		{
			p.SetState(373)
			p.Match(SpecGrammarParserCOMMA)
		}
		{
			p.SetState(374)
			p.Identifier()
		}

		p.SetState(379)
		p.GetErrorHandler().Sync(p)
		_la = p.GetTokenStream().LA(1)
	}

	return localctx
}

// IVarTypeTupleContext is an interface to support dynamic dispatch.
type IVarTypeTupleContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsVarTypeTupleContext differentiates from other interfaces.
	IsVarTypeTupleContext()
}

type VarTypeTupleContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyVarTypeTupleContext() *VarTypeTupleContext {
	var p = new(VarTypeTupleContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_varTypeTuple
	return p
}

func (*VarTypeTupleContext) IsVarTypeTupleContext() {}

func NewVarTypeTupleContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *VarTypeTupleContext {
	var p = new(VarTypeTupleContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_varTypeTuple

	return p
}

func (s *VarTypeTupleContext) GetParser() antlr.Parser { return s.parser }

func (s *VarTypeTupleContext) AllIdentifier() []IIdentifierContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IIdentifierContext)(nil)).Elem())
	var tst = make([]IIdentifierContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IIdentifierContext)
		}
	}

	return tst
}

func (s *VarTypeTupleContext) Identifier(i int) IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *VarTypeTupleContext) ElementType() IElementTypeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IElementTypeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IElementTypeContext)
}

func (s *VarTypeTupleContext) AllCOMMA() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserCOMMA)
}

func (s *VarTypeTupleContext) COMMA(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, i)
}

func (s *VarTypeTupleContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *VarTypeTupleContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *VarTypeTupleContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterVarTypeTuple(s)
	}
}

func (s *VarTypeTupleContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitVarTypeTuple(s)
	}
}

func (s *VarTypeTupleContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitVarTypeTuple(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) VarTypeTuple() (localctx IVarTypeTupleContext) {
	localctx = NewVarTypeTupleContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 68, SpecGrammarParserRULE_varTypeTuple)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(380)
		p.Identifier()
	}
	p.SetState(385)
	p.GetErrorHandler().Sync(p)
	_la = p.GetTokenStream().LA(1)

	for _la == SpecGrammarParserCOMMA {
		{
			p.SetState(381)
			p.Match(SpecGrammarParserCOMMA)
		}
		{
			p.SetState(382)
			p.Identifier()
		}

		p.SetState(387)
		p.GetErrorHandler().Sync(p)
		_la = p.GetTokenStream().LA(1)
	}
	{
		p.SetState(388)
		p.ElementType()
	}

	return localctx
}

// IAccessPermissionContext is an interface to support dynamic dispatch.
type IAccessPermissionContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsAccessPermissionContext differentiates from other interfaces.
	IsAccessPermissionContext()
}

type AccessPermissionContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyAccessPermissionContext() *AccessPermissionContext {
	var p = new(AccessPermissionContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_accessPermission
	return p
}

func (*AccessPermissionContext) IsAccessPermissionContext() {}

func NewAccessPermissionContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *AccessPermissionContext {
	var p = new(AccessPermissionContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_accessPermission

	return p
}

func (s *AccessPermissionContext) GetParser() antlr.Parser { return s.parser }

func (s *AccessPermissionContext) ACCESS() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserACCESS, 0)
}

func (s *AccessPermissionContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *AccessPermissionContext) Primary() IPrimaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPrimaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPrimaryContext)
}

func (s *AccessPermissionContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *AccessPermissionContext) Reference() IReferenceContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IReferenceContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IReferenceContext)
}

func (s *AccessPermissionContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *AccessPermissionContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *AccessPermissionContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterAccessPermission(s)
	}
}

func (s *AccessPermissionContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitAccessPermission(s)
	}
}

func (s *AccessPermissionContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitAccessPermission(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) AccessPermission() (localctx IAccessPermissionContext) {
	localctx = NewAccessPermissionContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 70, SpecGrammarParserRULE_accessPermission)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(400)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 29, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(390)
			p.Match(SpecGrammarParserACCESS)
		}
		{
			p.SetState(391)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(392)
			p.primary(0)
		}
		{
			p.SetState(393)
			p.Match(SpecGrammarParserRPAREN)
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(395)
			p.Match(SpecGrammarParserACCESS)
		}
		{
			p.SetState(396)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(397)
			p.Reference()
		}
		{
			p.SetState(398)
			p.Match(SpecGrammarParserRPAREN)
		}

	}

	return localctx
}

// IReferenceContext is an interface to support dynamic dispatch.
type IReferenceContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsReferenceContext differentiates from other interfaces.
	IsReferenceContext()
}

type ReferenceContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyReferenceContext() *ReferenceContext {
	var p = new(ReferenceContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_reference
	return p
}

func (*ReferenceContext) IsReferenceContext() {}

func NewReferenceContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *ReferenceContext {
	var p = new(ReferenceContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_reference

	return p
}

func (s *ReferenceContext) GetParser() antlr.Parser { return s.parser }

func (s *ReferenceContext) REFERENCE() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserREFERENCE, 0)
}

func (s *ReferenceContext) Primary() IPrimaryContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IPrimaryContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IPrimaryContext)
}

func (s *ReferenceContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *ReferenceContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *ReferenceContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterReference(s)
	}
}

func (s *ReferenceContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitReference(s)
	}
}

func (s *ReferenceContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitReference(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Reference() (localctx IReferenceContext) {
	localctx = NewReferenceContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 72, SpecGrammarParserRULE_reference)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(402)
		p.Match(SpecGrammarParserREFERENCE)
	}
	{
		p.SetState(403)
		p.primary(0)
	}

	return localctx
}

// IDomainContext is an interface to support dynamic dispatch.
type IDomainContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetKind returns the kind token.
	GetKind() antlr.Token

	// SetKind sets the kind token.
	SetKind(antlr.Token)

	// IsDomainContext differentiates from other interfaces.
	IsDomainContext()
}

type DomainContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
	kind   antlr.Token
}

func NewEmptyDomainContext() *DomainContext {
	var p = new(DomainContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_domain
	return p
}

func (*DomainContext) IsDomainContext() {}

func NewDomainContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *DomainContext {
	var p = new(DomainContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_domain

	return p
}

func (s *DomainContext) GetParser() antlr.Parser { return s.parser }

func (s *DomainContext) GetKind() antlr.Token { return s.kind }

func (s *DomainContext) SetKind(v antlr.Token) { s.kind = v }

func (s *DomainContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *DomainContext) AllDomain() []IDomainContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IDomainContext)(nil)).Elem())
	var tst = make([]IDomainContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IDomainContext)
		}
	}

	return tst
}

func (s *DomainContext) Domain(i int) IDomainContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IDomainContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IDomainContext)
}

func (s *DomainContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *DomainContext) DomainLiteral() IDomainLiteralContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IDomainLiteralContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IDomainLiteralContext)
}

func (s *DomainContext) AND() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserAND, 0)
}

func (s *DomainContext) OR() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserOR, 0)
}

func (s *DomainContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *DomainContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *DomainContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterDomain(s)
	}
}

func (s *DomainContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitDomain(s)
	}
}

func (s *DomainContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitDomain(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Domain() (localctx IDomainContext) {
	return p.domain(0)
}

func (p *SpecGrammarParser) domain(_p int) (localctx IDomainContext) {
	var _parentctx antlr.ParserRuleContext = p.GetParserRuleContext()
	_parentState := p.GetState()
	localctx = NewDomainContext(p, p.GetParserRuleContext(), _parentState)
	var _prevctx IDomainContext = localctx
	var _ antlr.ParserRuleContext = _prevctx // TODO: To prevent unused variable warning.
	_startState := 74
	p.EnterRecursionRule(localctx, 74, SpecGrammarParserRULE_domain, _p)

	defer func() {
		p.UnrollRecursionContexts(_parentctx)
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	var _alt int

	p.EnterOuterAlt(localctx, 1)
	p.SetState(411)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 30, p.GetParserRuleContext()) {
	case 1:
		{
			p.SetState(406)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(407)
			p.domain(0)
		}
		{
			p.SetState(408)
			p.Match(SpecGrammarParserRPAREN)
		}

	case 2:
		{
			p.SetState(410)
			p.DomainLiteral()
		}

	}
	p.GetParserRuleContext().SetStop(p.GetTokenStream().LT(-1))
	p.SetState(421)
	p.GetErrorHandler().Sync(p)
	_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 32, p.GetParserRuleContext())

	for _alt != 2 && _alt != antlr.ATNInvalidAltNumber {
		if _alt == 1 {
			if p.GetParseListeners() != nil {
				p.TriggerExitRuleEvent()
			}
			_prevctx = localctx
			p.SetState(419)
			p.GetErrorHandler().Sync(p)
			switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 31, p.GetParserRuleContext()) {
			case 1:
				localctx = NewDomainContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_domain)
				p.SetState(413)

				if !(p.Precpred(p.GetParserRuleContext(), 3)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 3)", ""))
				}
				{
					p.SetState(414)

					var _m = p.Match(SpecGrammarParserAND)

					localctx.(*DomainContext).kind = _m
				}
				{
					p.SetState(415)
					p.domain(4)
				}

			case 2:
				localctx = NewDomainContext(p, _parentctx, _parentState)
				p.PushNewRecursionContext(localctx, _startState, SpecGrammarParserRULE_domain)
				p.SetState(416)

				if !(p.Precpred(p.GetParserRuleContext(), 2)) {
					panic(antlr.NewFailedPredicateException(p, "p.Precpred(p.GetParserRuleContext(), 2)", ""))
				}
				{
					p.SetState(417)

					var _m = p.Match(SpecGrammarParserOR)

					localctx.(*DomainContext).kind = _m
				}
				{
					p.SetState(418)
					p.domain(3)
				}

			}

		}
		p.SetState(423)
		p.GetErrorHandler().Sync(p)
		_alt = p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 32, p.GetParserRuleContext())
	}

	return localctx
}

// IDomainLiteralContext is an interface to support dynamic dispatch.
type IDomainLiteralContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsDomainLiteralContext differentiates from other interfaces.
	IsDomainLiteralContext()
}

type DomainLiteralContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyDomainLiteralContext() *DomainLiteralContext {
	var p = new(DomainLiteralContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_domainLiteral
	return p
}

func (*DomainLiteralContext) IsDomainLiteralContext() {}

func NewDomainLiteralContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *DomainLiteralContext {
	var p = new(DomainLiteralContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_domainLiteral

	return p
}

func (s *DomainLiteralContext) GetParser() antlr.Parser { return s.parser }

func (s *DomainLiteralContext) NumericDomainLiteral() INumericDomainLiteralContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*INumericDomainLiteralContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(INumericDomainLiteralContext)
}

func (s *DomainLiteralContext) DataStructureDomainLiteral() IDataStructureDomainLiteralContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IDataStructureDomainLiteralContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IDataStructureDomainLiteralContext)
}

func (s *DomainLiteralContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *DomainLiteralContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *DomainLiteralContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterDomainLiteral(s)
	}
}

func (s *DomainLiteralContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitDomainLiteral(s)
	}
}

func (s *DomainLiteralContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitDomainLiteral(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) DomainLiteral() (localctx IDomainLiteralContext) {
	localctx = NewDomainLiteralContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 76, SpecGrammarParserRULE_domainLiteral)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(426)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 33, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(424)
			p.NumericDomainLiteral()
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(425)
			p.DataStructureDomainLiteral()
		}

	}

	return localctx
}

// INumericDomainLiteralContext is an interface to support dynamic dispatch.
type INumericDomainLiteralContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// GetLowerKind returns the lowerKind token.
	GetLowerKind() antlr.Token

	// GetUpperKind returns the upperKind token.
	GetUpperKind() antlr.Token

	// SetLowerKind sets the lowerKind token.
	SetLowerKind(antlr.Token)

	// SetUpperKind sets the upperKind token.
	SetUpperKind(antlr.Token)

	// IsNumericDomainLiteralContext differentiates from other interfaces.
	IsNumericDomainLiteralContext()
}

type NumericDomainLiteralContext struct {
	*antlr.BaseParserRuleContext
	parser    antlr.Parser
	lowerKind antlr.Token
	upperKind antlr.Token
}

func NewEmptyNumericDomainLiteralContext() *NumericDomainLiteralContext {
	var p = new(NumericDomainLiteralContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_numericDomainLiteral
	return p
}

func (*NumericDomainLiteralContext) IsNumericDomainLiteralContext() {}

func NewNumericDomainLiteralContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *NumericDomainLiteralContext {
	var p = new(NumericDomainLiteralContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_numericDomainLiteral

	return p
}

func (s *NumericDomainLiteralContext) GetParser() antlr.Parser { return s.parser }

func (s *NumericDomainLiteralContext) GetLowerKind() antlr.Token { return s.lowerKind }

func (s *NumericDomainLiteralContext) GetUpperKind() antlr.Token { return s.upperKind }

func (s *NumericDomainLiteralContext) SetLowerKind(v antlr.Token) { s.lowerKind = v }

func (s *NumericDomainLiteralContext) SetUpperKind(v antlr.Token) { s.upperKind = v }

func (s *NumericDomainLiteralContext) AllExpression() []IExpressionContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IExpressionContext)(nil)).Elem())
	var tst = make([]IExpressionContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IExpressionContext)
		}
	}

	return tst
}

func (s *NumericDomainLiteralContext) Expression(i int) IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *NumericDomainLiteralContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *NumericDomainLiteralContext) AllLEQ() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserLEQ)
}

func (s *NumericDomainLiteralContext) LEQ(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLEQ, i)
}

func (s *NumericDomainLiteralContext) AllLESS() []antlr.TerminalNode {
	return s.GetTokens(SpecGrammarParserLESS)
}

func (s *NumericDomainLiteralContext) LESS(i int) antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLESS, i)
}

func (s *NumericDomainLiteralContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *NumericDomainLiteralContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *NumericDomainLiteralContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterNumericDomainLiteral(s)
	}
}

func (s *NumericDomainLiteralContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitNumericDomainLiteral(s)
	}
}

func (s *NumericDomainLiteralContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitNumericDomainLiteral(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) NumericDomainLiteral() (localctx INumericDomainLiteralContext) {
	localctx = NewNumericDomainLiteralContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 78, SpecGrammarParserRULE_numericDomainLiteral)
	var _la int

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(428)
		p.Expression()
	}
	{
		p.SetState(429)

		var _lt = p.GetTokenStream().LT(1)

		localctx.(*NumericDomainLiteralContext).lowerKind = _lt

		_la = p.GetTokenStream().LA(1)

		if !(_la == SpecGrammarParserLESS || _la == SpecGrammarParserLEQ) {
			var _ri = p.GetErrorHandler().RecoverInline(p)

			localctx.(*NumericDomainLiteralContext).lowerKind = _ri
		} else {
			p.GetErrorHandler().ReportMatch(p)
			p.Consume()
		}
	}
	{
		p.SetState(430)
		p.Identifier()
	}
	{
		p.SetState(431)

		var _lt = p.GetTokenStream().LT(1)

		localctx.(*NumericDomainLiteralContext).upperKind = _lt

		_la = p.GetTokenStream().LA(1)

		if !(_la == SpecGrammarParserLESS || _la == SpecGrammarParserLEQ) {
			var _ri = p.GetErrorHandler().RecoverInline(p)

			localctx.(*NumericDomainLiteralContext).upperKind = _ri
		} else {
			p.GetErrorHandler().ReportMatch(p)
			p.Consume()
		}
	}
	{
		p.SetState(432)
		p.Expression()
	}

	return localctx
}

// IDataStructureDomainLiteralContext is an interface to support dynamic dispatch.
type IDataStructureDomainLiteralContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsDataStructureDomainLiteralContext differentiates from other interfaces.
	IsDataStructureDomainLiteralContext()
}

type DataStructureDomainLiteralContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyDataStructureDomainLiteralContext() *DataStructureDomainLiteralContext {
	var p = new(DataStructureDomainLiteralContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_dataStructureDomainLiteral
	return p
}

func (*DataStructureDomainLiteralContext) IsDataStructureDomainLiteralContext() {}

func NewDataStructureDomainLiteralContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *DataStructureDomainLiteralContext {
	var p = new(DataStructureDomainLiteralContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_dataStructureDomainLiteral

	return p
}

func (s *DataStructureDomainLiteralContext) GetParser() antlr.Parser { return s.parser }

func (s *DataStructureDomainLiteralContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *DataStructureDomainLiteralContext) AllIdentifier() []IIdentifierContext {
	var ts = s.GetTypedRuleContexts(reflect.TypeOf((*IIdentifierContext)(nil)).Elem())
	var tst = make([]IIdentifierContext, len(ts))

	for i, t := range ts {
		if t != nil {
			tst[i] = t.(IIdentifierContext)
		}
	}

	return tst
}

func (s *DataStructureDomainLiteralContext) Identifier(i int) IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), i)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *DataStructureDomainLiteralContext) COMMA() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserCOMMA, 0)
}

func (s *DataStructureDomainLiteralContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *DataStructureDomainLiteralContext) DataStructureRange() IDataStructureRangeContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IDataStructureRangeContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IDataStructureRangeContext)
}

func (s *DataStructureDomainLiteralContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *DataStructureDomainLiteralContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *DataStructureDomainLiteralContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterDataStructureDomainLiteral(s)
	}
}

func (s *DataStructureDomainLiteralContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitDataStructureDomainLiteral(s)
	}
}

func (s *DataStructureDomainLiteralContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitDataStructureDomainLiteral(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) DataStructureDomainLiteral() (localctx IDataStructureDomainLiteralContext) {
	localctx = NewDataStructureDomainLiteralContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 80, SpecGrammarParserRULE_dataStructureDomainLiteral)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(449)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 34, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(434)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(435)
			p.Identifier()
		}
		{
			p.SetState(436)
			p.Match(SpecGrammarParserCOMMA)
		}
		{
			p.SetState(437)
			p.Identifier()
		}
		{
			p.SetState(438)
			p.Match(SpecGrammarParserRPAREN)
		}
		{
			p.SetState(439)
			p.DataStructureRange()
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(441)
			p.Identifier()
		}
		{
			p.SetState(442)
			p.Match(SpecGrammarParserCOMMA)
		}
		{
			p.SetState(443)
			p.Identifier()
		}
		{
			p.SetState(444)
			p.DataStructureRange()
		}

	case 3:
		p.EnterOuterAlt(localctx, 3)
		{
			p.SetState(446)
			p.Identifier()
		}
		{
			p.SetState(447)
			p.DataStructureRange()
		}

	}

	return localctx
}

// IDataStructureRangeContext is an interface to support dynamic dispatch.
type IDataStructureRangeContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsDataStructureRangeContext differentiates from other interfaces.
	IsDataStructureRangeContext()
}

type DataStructureRangeContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyDataStructureRangeContext() *DataStructureRangeContext {
	var p = new(DataStructureRangeContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_dataStructureRange
	return p
}

func (*DataStructureRangeContext) IsDataStructureRangeContext() {}

func NewDataStructureRangeContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *DataStructureRangeContext {
	var p = new(DataStructureRangeContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_dataStructureRange

	return p
}

func (s *DataStructureRangeContext) GetParser() antlr.Parser { return s.parser }

func (s *DataStructureRangeContext) IN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserIN, 0)
}

func (s *DataStructureRangeContext) RANGE() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRANGE, 0)
}

func (s *DataStructureRangeContext) Expression() IExpressionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IExpressionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IExpressionContext)
}

func (s *DataStructureRangeContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *DataStructureRangeContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *DataStructureRangeContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterDataStructureRange(s)
	}
}

func (s *DataStructureRangeContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitDataStructureRange(s)
	}
}

func (s *DataStructureRangeContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitDataStructureRange(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) DataStructureRange() (localctx IDataStructureRangeContext) {
	localctx = NewDataStructureRangeContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 82, SpecGrammarParserRULE_dataStructureRange)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.EnterOuterAlt(localctx, 1)
	{
		p.SetState(451)
		p.Match(SpecGrammarParserIN)
	}
	{
		p.SetState(452)
		p.Match(SpecGrammarParserRANGE)
	}
	{
		p.SetState(453)
		p.Expression()
	}

	return localctx
}

// IPredicateContext is an interface to support dynamic dispatch.
type IPredicateContext interface {
	antlr.ParserRuleContext

	// GetParser returns the parser.
	GetParser() antlr.Parser

	// IsPredicateContext differentiates from other interfaces.
	IsPredicateContext()
}

type PredicateContext struct {
	*antlr.BaseParserRuleContext
	parser antlr.Parser
}

func NewEmptyPredicateContext() *PredicateContext {
	var p = new(PredicateContext)
	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(nil, -1)
	p.RuleIndex = SpecGrammarParserRULE_predicate
	return p
}

func (*PredicateContext) IsPredicateContext() {}

func NewPredicateContext(parser antlr.Parser, parent antlr.ParserRuleContext, invokingState int) *PredicateContext {
	var p = new(PredicateContext)

	p.BaseParserRuleContext = antlr.NewBaseParserRuleContext(parent, invokingState)

	p.parser = parser
	p.RuleIndex = SpecGrammarParserRULE_predicate

	return p
}

func (s *PredicateContext) GetParser() antlr.Parser { return s.parser }

func (s *PredicateContext) PREDICATE() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserPREDICATE, 0)
}

func (s *PredicateContext) Identifier() IIdentifierContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IIdentifierContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IIdentifierContext)
}

func (s *PredicateContext) LPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLPAREN, 0)
}

func (s *PredicateContext) VariableList() IVariableListContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IVariableListContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IVariableListContext)
}

func (s *PredicateContext) RPAREN() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRPAREN, 0)
}

func (s *PredicateContext) LCB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserLCB, 0)
}

func (s *PredicateContext) Assertion() IAssertionContext {
	var t = s.GetTypedRuleContext(reflect.TypeOf((*IAssertionContext)(nil)).Elem(), 0)

	if t == nil {
		return nil
	}

	return t.(IAssertionContext)
}

func (s *PredicateContext) RCB() antlr.TerminalNode {
	return s.GetToken(SpecGrammarParserRCB, 0)
}

func (s *PredicateContext) GetRuleContext() antlr.RuleContext {
	return s
}

func (s *PredicateContext) ToStringTree(ruleNames []string, recog antlr.Recognizer) string {
	return antlr.TreesStringTree(s, ruleNames, recog)
}

func (s *PredicateContext) EnterRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.EnterPredicate(s)
	}
}

func (s *PredicateContext) ExitRule(listener antlr.ParseTreeListener) {
	if listenerT, ok := listener.(SpecGrammarListener); ok {
		listenerT.ExitPredicate(s)
	}
}

func (s *PredicateContext) Accept(visitor antlr.ParseTreeVisitor) interface{} {
	switch t := visitor.(type) {
	case SpecGrammarVisitor:
		return t.VisitPredicate(s)

	default:
		return t.VisitChildren(s)
	}
}

func (p *SpecGrammarParser) Predicate() (localctx IPredicateContext) {
	localctx = NewPredicateContext(p, p.GetParserRuleContext(), p.GetState())
	p.EnterRule(localctx, 84, SpecGrammarParserRULE_predicate)

	defer func() {
		p.ExitRule()
	}()

	defer func() {
		if err := recover(); err != nil {
			if v, ok := err.(antlr.RecognitionException); ok {
				localctx.SetException(v)
				p.GetErrorHandler().ReportError(p, v)
				p.GetErrorHandler().Recover(p, v)
			} else {
				panic(err)
			}
		}
	}()

	p.SetState(472)
	p.GetErrorHandler().Sync(p)
	switch p.GetInterpreter().AdaptivePredict(p.GetTokenStream(), 35, p.GetParserRuleContext()) {
	case 1:
		p.EnterOuterAlt(localctx, 1)
		{
			p.SetState(455)
			p.Match(SpecGrammarParserPREDICATE)
		}
		{
			p.SetState(456)
			p.Identifier()
		}
		{
			p.SetState(457)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(458)
			p.VariableList()
		}
		{
			p.SetState(459)
			p.Match(SpecGrammarParserRPAREN)
		}
		{
			p.SetState(460)
			p.Match(SpecGrammarParserLCB)
		}
		{
			p.SetState(461)
			p.assertion(0)
		}
		{
			p.SetState(462)
			p.Match(SpecGrammarParserRCB)
		}

	case 2:
		p.EnterOuterAlt(localctx, 2)
		{
			p.SetState(464)
			p.Match(SpecGrammarParserPREDICATE)
		}
		{
			p.SetState(465)
			p.Identifier()
		}
		{
			p.SetState(466)
			p.Match(SpecGrammarParserLPAREN)
		}
		{
			p.SetState(467)
			p.Match(SpecGrammarParserRPAREN)
		}
		{
			p.SetState(468)
			p.Match(SpecGrammarParserLCB)
		}
		{
			p.SetState(469)
			p.assertion(0)
		}
		{
			p.SetState(470)
			p.Match(SpecGrammarParserRCB)
		}

	}

	return localctx
}

func (p *SpecGrammarParser) Sempred(localctx antlr.RuleContext, ruleIndex, predIndex int) bool {
	switch ruleIndex {
	case 3:
		var t *AssertionContext = nil
		if localctx != nil {
			t = localctx.(*AssertionContext)
		}
		return p.Assertion_Sempred(t, predIndex)

	case 5:
		var t *PrimaryContext = nil
		if localctx != nil {
			t = localctx.(*PrimaryContext)
		}
		return p.Primary_Sempred(t, predIndex)

	case 7:
		var t *BinaryContext = nil
		if localctx != nil {
			t = localctx.(*BinaryContext)
		}
		return p.Binary_Sempred(t, predIndex)

	case 37:
		var t *DomainContext = nil
		if localctx != nil {
			t = localctx.(*DomainContext)
		}
		return p.Domain_Sempred(t, predIndex)

	default:
		panic("No predicate with index: " + fmt.Sprint(ruleIndex))
	}
}

func (p *SpecGrammarParser) Assertion_Sempred(localctx antlr.RuleContext, predIndex int) bool {
	switch predIndex {
	case 0:
		return p.Precpred(p.GetParserRuleContext(), 4)

	case 1:
		return p.Precpred(p.GetParserRuleContext(), 3)

	default:
		panic("No predicate with index: " + fmt.Sprint(predIndex))
	}
}

func (p *SpecGrammarParser) Primary_Sempred(localctx antlr.RuleContext, predIndex int) bool {
	switch predIndex {
	case 2:
		return p.Precpred(p.GetParserRuleContext(), 3)

	case 3:
		return p.Precpred(p.GetParserRuleContext(), 2)

	case 4:
		return p.Precpred(p.GetParserRuleContext(), 1)

	default:
		panic("No predicate with index: " + fmt.Sprint(predIndex))
	}
}

func (p *SpecGrammarParser) Binary_Sempred(localctx antlr.RuleContext, predIndex int) bool {
	switch predIndex {
	case 5:
		return p.Precpred(p.GetParserRuleContext(), 7)

	case 6:
		return p.Precpred(p.GetParserRuleContext(), 6)

	case 7:
		return p.Precpred(p.GetParserRuleContext(), 5)

	case 8:
		return p.Precpred(p.GetParserRuleContext(), 4)

	case 9:
		return p.Precpred(p.GetParserRuleContext(), 3)

	case 10:
		return p.Precpred(p.GetParserRuleContext(), 2)

	default:
		panic("No predicate with index: " + fmt.Sprint(predIndex))
	}
}

func (p *SpecGrammarParser) Domain_Sempred(localctx antlr.RuleContext, predIndex int) bool {
	switch predIndex {
	case 11:
		return p.Precpred(p.GetParserRuleContext(), 3)

	case 12:
		return p.Precpred(p.GetParserRuleContext(), 2)

	default:
		panic("No predicate with index: " + fmt.Sprint(predIndex))
	}
}
