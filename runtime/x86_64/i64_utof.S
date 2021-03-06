// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, INRIA Paris
//
// Copyright (c) 2016 Institut National de Recherche en Informatique et
//  en Automatique.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the <organization> nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
// HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// *********************************************************************

// Helper functions for 64-bit integer arithmetic.  x86_64 version.
	
#include "sysdeps.h"

// Conversion unsigned long -> single-precision float

FUNCTION(__compcert_i64_utof)
        testq   INT_ARG_1, INT_ARG_1
        js      1f
        pxor    FP_RES, FP_RES          // if < 2^63,
        cvtsi2ssq INT_ARG_1, FP_RES     // convert as if signed
        ret
1:                                      // if >= 2^63, use round-to-odd trick
        movq    INT_ARG_1, %rax
        shrq    %rax
        andq    $1, INT_ARG_1
        orq     INT_ARG_1, %rax         // (arg >> 1) | (arg & 1)
        pxor    FP_RES, FP_RES
        cvtsi2ssq %rax, FP_RES          // convert as if signed
        addss   FP_RES, FP_RES          // multiply result by 2.0
        ret
ENDFUNCTION(__compcert_i64_utof)       
