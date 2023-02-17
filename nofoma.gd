#########################################################################
##
#A  nofoma.gd                                                Meinolf Geck
##
#Y  Copyright (C) 2019/22  Lehrstuhl fuer Algebra, Universitaet Stuttgart
##
##  This is a package for computing maximal vectors, minimal polynomials, 
##  the rational canonical form (or Frobenius normal form)  and also  the
##  Jordan-Chevalley decomposition  of a  matrix  over any  field that is 
##  available in  GAP. The algorithms are based on, and a combination of:  
## 
##  K. Bongartz,  A direct approach to the rational normal form, preprint
##                                          available at arXiv:1410.1683.
## 
##  M. Neunhoeffer and  C. E. Praeger,  Computing minimal polynomials  of
##                     matrices, LMS J. Comput. Math. 11 (2008), 252-279;
## 
##  M. Geck,  On Jacob's construction  of  the  rational  canonical form, 
##                        Electron. J. Linear Algebra 36 (2020), 177-182.
##  
##  M. Geck, On the Jordan-Chevalley decomposition of a matrix, preprint.
##
##  Stuttgart, June 1, 2022.
#########################################################################

#! @Chapter The nofoma package
#! @ChapterLabel The nofoma package
#! @Section Maximal vectors and normal forms
#! Let <M>K</M> be a field and <M>A</M> be an <M>n\times n</M>-matrix over 
#! <M>K</M>. This package provides functions for computing a maximal vector
#! for <M>A</M>, the Frobenius normal form of <M>A</M> and the 
#! Jordan-Chevalley decomposition of <M>A</M>.
#! 
#! For any (row) vector <M>v\in K^n</M>, the local minimal polynomial is the 
#! unique monic polynomial <M>f\in K[X]</M> of smallest possible degree such 
#! that <M>v.f(A)=0</M>. (Note that, as usual in GAP, matrices act on the 
#! right on row vectors.) It is known that there always exists a 
#! <M>v\in K^n</M> such that the local minimal polynomial of <M>v</M> equals 
#! the minimal polynomial of <M>A</M>; such a <M>v</M> is called a 'maximal 
#! vector' for <M>A</M>. 
#! 
#! The currently best algorithm for computing the minimal polynomial of 
#! <M>A</M> is probably that of Neunhoeffer--Praeger (already implemented 
#! in GAP). One of the purposes of this package is to modify that algorithm 
#! so that it also includes the computation of a maximal vector for <M>A</M>; 
#! this is done by the function 'MaximalVectorMat'. Once this is available, 
#! the Frobenius normal form (or rational canonical form) of <M>A</M> can be 
#! computed efficiently by a recursive algorithm. 
#! 
#! Finally, we also provide a function for computing the Jordan-Chevalley
#! decomposition of <M>A</M>. Usually, this is obtained as a consequence of 
#! the Jordan normal form of <M>A</M>, but in general the latter is difficult 
#! to compute because one needs to know the eigenvalues of <M>A</M>. However,
#! there is an elegant algorithmic approach (going back to Chevalley), which 
#! is inspired by the Newton iteration for finding the zeroes of a function;
#! and it does not require the knowledge of the eigenvalues of <M>A</M>. This
#! is implemented in the function 'JordanChevalleyDecMat'.
#! 
#! Further references are provided within the help menu of each function.
#! 
#! Any comments welcome!                            Meinolf Geck, June 2022
#! 
#! @Section Copyright and installation of the nofoma package
#! The nofoma package is free software; you can redistribute it and/or 
#! modify it under the terms of the GNU General Public License as published 
#! by the Free Software Foundation; either version 2 of the License, or (at 
#! your option) any later version.
#!
#! To install this package first unpack it inside some GAP root directory
#! in the subdirectory 'pkg' (see the section 'Installing a GAP Package' of
#! the GAP reference manual). Then 'nofoma' can already be loaded and used
#! (just type LoadPackage("nofoma");).
#!
#! @Section The main functions

DeclareInfoClass("Infonofoma"); 
##  Since 'Info' does unwanted formatting, we use (from EDIM package):
DeclareGlobalFunction("IInofoma");
DeclareGlobalFunction("nfmCoeffsPol"); 
DeclareGlobalFunction("nfmPolCoeffs");
DeclareGlobalFunction("nfmGcd");
DeclareGlobalFunction("nfmLcm");
DeclareGlobalFunction("GcdCoprimeSplit");
DeclareGlobalFunction("PolynomialToMatVec");
DeclareGlobalFunction("PolynomialToMat");
DeclareGlobalFunction("LcmMaximalVectorMat");
DeclareGlobalFunction("SpinMatVector1");

#! @Arguments A,v
#! @Description
#! 'SpinMatVector' computes  the  smallest subspace containing the vector  
#!  <A>v</A> that is invariant under the matrix <A>A</A>. The  output is a 
#!  quadruple, with 
#!  * 1st component = basis of that subspace in row echelon form; 
#!  * 2nd component = matrix  with  rows <M>v</M>, <M>v.A</M>, <M>v.A^2</M>, 
#!     ..., <M>v.A^{{d-1}}</M> (where <M>d</M> is the degree of the local 
#!     minimal polynomial of <A>v</A>); 
#!  * 3rd component = the coefficients <M>a_0</M>, <M>a_1</M>, ..., 
#!     <M>a_d</M> of the local minimal polynomial; and 
#!  * 4th component = the positions of the pivots of the first component.
#! 
#! @BeginExampleSession
#! gap> A:=[ [   5,   2,  -4,   2 ],
#! >         [  -1,   0,   2,  -1 ],
#! >         [  -1,  -1,   3,  -1 ],
#! >         [ -13,  -7,  14,  -6 ] ];
#! gap> SpinMatVector(a,[1,0,0,0]);
#! [ [ [ 1, 0, 0, 0 ], [ 0, 1, -2, 1 ] ], 
#!   [ [ 1, 0, 0, 0 ], [ 5, 2, -4, 2 ] ], 
#!   [ -1, 0, 1 ],             # local min. pol. is X^2-1
#!   [ 1, 2 ] ]                # pivots
#! gap> SpinMatVector(a,[0,1,0,0]);
#! [ [ [ 0, 1, 0, 0 ], [ 1, 0, -2, 1 ], [ 0, 0, 1, -1/2 ] ], 
#!   [ [ 0, 1, 0, 0 ], [ -1, 0, 2, -1 ], [ 6, 3, -4, 2 ] ], 
#!   [ 1, -1, -1, 1 ],         # local min. pol. is X^3-X^2-X^2+1
#!   [ 2, 1, 3 ] ]             # pivots
#! gap> SpinMatVector(a,[1,1,0,0]);
#! [ [ [ 1, 1, 0, 0 ], [ 0, 1, 1, -1/2 ] ], 
#!   [ [ 1, 1, 0, 0 ], [ 4, 2, -2, 1 ] ], 
#!   [ 1, -2, 1 ],             # local min. pol. is X^2-2X+1
#!   [ 1, 2 ] ]                # pivots
#! @EndExampleSession
DeclareGlobalFunction("SpinMatVector");

DeclareGlobalFunction("CyclicChainMat");
DeclareGlobalFunction("nfmRelMinPols");
DeclareGlobalFunction("nfmOrderPolM");
DeclareGlobalFunction("MinPolyMat");

#! @Arguments A
#! @Description
#!  'MaximalVectorMat' returns the minimal polynomial and a maximal vector 
#!  of the matrix <A>A</A>, that is, a vector whose local minimal polynomial 
#!  is that of <A>A</A>. This is done by repeatedly spinning up vectors until 
#!  a maximal one is found. The exact algorithm is a combination of 
#!  * the minimal polynomial algorithm by Neunhoeffer-Praeger; see 
#!      J. Comput. Math. 11, 2008 
#!      (<URL>http://doi.org/10.1112/S1461157000000590</URL>); and  
#!  * the method described by Bongartz 
#!      (see <URL>https://arxiv.org/abs/1410.1683</URL>) for computing 
#!      maximal vectors.
#!
#!  See also the article by Geck at
#!  <URL>https://doi.org/10.13001/ela.2020.5055</URL>. 
#!
#! @BeginExampleSession
#! gap> A:=[ [  2,  2,  0,  1,  0,  2,  1 ],
#! >         [  0,  4,  0,  0,  0,  1,  0 ],
#! >         [  0,  1,  1,  0,  0,  1,  1 ],
#! >         [  0, -1,  0,  1,  0, -1,  0 ],
#! >         [  0, -7,  0,  0,  1, -5,  0 ],
#! >         [  0, -2,  0,  0,  0,  1,  0 ],
#! >         [  0, -1,  0,  0,  0, -1,  1 ] ];
#! # (Example taken from Ballester-Bolinches et al., Oper. Matrices 12, 2018.)
#! gap> MaximalVectorMat(A);
#! [ [ 1, -2, 1, 1, 0, 0, 1 ], x_1^4-7*x_1^3+17*x_1^2-17*x_1+6 ]
#! gap> v:=last[1];                    # maximal vector for A
#! gap> SpinMatVector(A,v)[3];         # check result: 3rd component = 
#! [ 6, -17, 17, -7, 1 ]               #   coeffs of local minimal polynomial       
#! @EndExampleSession
#! In the following example, <M>M_2</M> is the (challenging) test matrix 
#! from the paper by Neunhoeffer-Praeger:
#!
#! @BeginExampleSession
#! gap> LoadPackage("AtlasRep");; g:=AtlasGroup("B",1); M2:=g.1+g.2+g.1*g.2;
#! <matrix group of size 4154781481226426191177580544000000 with 2 generators>
#! <an immutable 4370x4370 matrix over GF2>
#! gap> SetInfoLevel(Infonofoma,1);
#! gap> MaximalVectorMat(M2);;time;
#! #I Degree of minimal polynomial is 2097
#! 6725
#! gap> MinimalPolynomial(M2);;time;        # built-in GAP function
#! 13415
#! gap> LoadPackage("cvec");                # package compact vectors
#! gap> MinimalPolynomial(CMat(M2));;time;   
#! 9721
#! @EndExampleSession
DeclareGlobalFunction("MaximalVectorMat");

DeclareGlobalFunction("JacobMatComplement");
DeclareGlobalFunction("BuildBlockDiagonalMat");
DeclareGlobalFunction("BuildBlockDiagonalMat1");
DeclareGlobalFunction("RatFormStep1");
DeclareGlobalFunction("RatFormStep1J");
DeclareGlobalFunction("nfmCompanionMat");
DeclareGlobalFunction("nfmCompanionMat1");

#! @Arguments A
#! @Description
#!  'FrobeniusNormalForm' returns the invariant factors of a matrix <A>A</A>
#!  and an invertible matrix <M>P</M> such that <M>P.A.P^{{-1}}</M> is the 
#!  Frobenius normal form of <A>A</A>. The algorithm first computes a maximal 
#!  vector and an <A>A</A>-invariant complement following Jacob's construction
#!  (as described in matrix language in Geck, Electron. J. Linear Algebra 36, 
#!  2020, <URL>https://doi.org/10.13001/ela.2020.5055</URL>); then the 
#!  algorithm continues recursively. It works for matrices over any field 
#!  that is available in GAP. The output is a triple with 
#!  * 1st component  = list of invariant factors; 
#!  * 2nd component = base change matrix <M>P</M>; and 
#!  * 3rd component = indices where the various blocks in the normal form 
#!       begin.
#! 
#! @BeginExampleSession
#! gap> A:=[ [  2,  2,  0,  1,  0,  2,  1 ],
#! >         [  0,  4,  0,  0,  0,  1,  0 ],
#! >         [  0,  1,  1,  0,  0,  1,  1 ],
#! >         [  0, -1,  0,  1,  0, -1,  0 ],
#! >         [  0, -7,  0,  0,  1, -5,  0 ],
#! >         [  0, -2,  0,  0,  0,  1,  0 ],
#! >         [  0, -1,  0,  0,  0, -1,  1 ] ];
#! gap> f:=FrobeniusNormalForm(A);
#! [ [ x_1^4-7*x_1^3+17*x_1^2-17*x_1+6, x_1^2-3*x_1+2, x_1-1 ], 
#!                                  # f[1] = List of invariant factors
#!   [ [    1,   -2,    1,    1,    0,    0,    1 ],
#!     [    2,   -7,    1,    2,    0,   -1,    3 ],
#!     [    4,  -26,    1,    4,    0,   -8,    6 ],
#!     [    8,  -89,    1,    8,    0,  -35,   11 ],
#!     [ -1/2,   -2,    0,  1/2,    0,   -2, -3/2 ],
#!     [   -1,   -4,    0,    0,    0,   -4,   -2 ],
#!     [    0,  9/4,    0,   -3,    1,  5/4,  1/4 ] ],
#!                                  # f[2] = base change matrix P
#!   [ 1, 5, 7 ]  ]                 # f[3] = indices where the blocks begin
#! gap> PrintArray(f[2]*A*f[2]^-1);
#! [ [   0,   1,   0,   0,   0,   0,   0 ], 
#!   [   0,   0,   1,   0,   0,   0,   0 ],
#!   [   0,   0,   0,   1,   0,   0,   0 ],
#!   [  -6,  17, -17,   7,   0,   0,   0 ],
#!   [   0,   0,   0,   0,   0,   1,   0 ],
#!   [   0,   0,   0,   0,  -2,   3,   0 ],
#!   [   0,   0,   0,   0,   0,   0,   1 ] ]
#! (This is the Frobenius normal form; there are 3 diagonal blocks,
#!  one of size 4, one of size 2 and one of size 1.)
#! @EndExampleSession
#! 
#! You can also use  'CreateNormalForm( f[1] );' to produce the Frobenius
#! normal form. (This function just builds the block diagonal matrix with 
#! diagonal blocks given by the companion matrices corresponding to the 
#! various invariant factors of <A>A</A>.) 
DeclareGlobalFunction("FrobeniusNormalForm");

DeclareGlobalFunction("CreateNormalForm");
DeclareGlobalFunction("FrobeniusNormalForm1");
DeclareGlobalFunction("InvariantFactorsMat");
DeclareGlobalFunction("nfmFrobInv");
DeclareGlobalFunction("SquareFreePol");

#! @Arguments A,f
#! @Description
#!  'JordanChevalleyDecMat' returns the unique pair of matrices <M>D</M>, 
#!  <M>N</M> such that the matrix <A>A</A> is written as <M>A=D+N</M>, where 
#!  <M>N</M> is a nilpotent matrix and <M>D</M> is a matrix that is 
#!  diagonalisable (over some extension field of the default field of 
#!  <A>A</A>), such that <M>D.N=N.D</M>; the argument <A>f</A> is a 
#!  polynomial such that <M>f(A)=0</M> (e.g., the minimal polynomial of 
#!  <A>A</A>). This is called the Jordan-Chevalley decomposition of <A>A</A>; 
#!  the algorithm is based on the preprint at 
#!  <URL>https://arxiv.org/abs/2205.05432</URL>. Note that this 
#!  algorithm does not require the knowledge of the eigenvalues of <A>A</A>; 
#!  it works over any perfect field that is available in GAP.
#!
#! @BeginExampleSession
#! gap> A:=[ [  6, -2,  6,  1,  1 ],
#! >         [  1, -1,  2,  1, -2 ],
#! >         [ -2,  0, -1,  0, -1 ],
#! >         [ -1,  0, -2,  2, -1 ],
#! >         [ -4,  4, -6, -2,  3 ] ];
#! gap> jc:=JordanChevalleyDecMat(A,MinimalPolynomial(A));
#! [ [ [  4,  0,  4, -1,  1 ], 
#!     [  1,  0,  1,  1, -1 ], 
#!     [ -1, -1,  0,  1, -1 ], 
#!     [  0,  0, -2,  3,  0 ], 
#!     [ -3,  2, -4, -1,  2 ] ], 
#!   [ [  2, -2,  2,  2,  0 ], 
#!     [  0, -1,  1,  0, -1 ], 
#!     [ -1,  1, -1, -1,  0 ], 
#!     [ -1,  0,  0, -1, -1 ], 
#!     [ -1,  2, -2, -1,  1 ] ] ]
#! gap> MinimalPolynomial(jc[1]);
#! x_1^3-5*x_1^2+9*x_1-5
#! gap> Factors(last);
#! [ x_1-1, x_1^2-4*x_1+5 ]   # diagonalisable over quadratic extension of Q
#! gap> MinimalPolynomial(jc[2]);
#! x_1^2                      # nilpotent
#! @EndExampleSession
#!  If the input matrix is very large, then 'JordanChevalleyDecMatF(<A>A</A>);' 
#!  may be more efficient; this function first computes the Frobenius normal 
#!  form of <A>A</A> and then applies 'JordanChevalleyDecMat' to each diagonal 
#!  block. (The result will be the same as that of 
#!  'JordanChevalleyDecMat(<A>A</A>);)'
DeclareGlobalFunction("JordanChevalleyDecMat");

DeclareGlobalFunction("JordanChevalleyDecMatF");
DeclareGlobalFunction("CheckFrobForm");
DeclareGlobalFunction("CheckJordanChev");

#! @Arguments lev
#! @Description
#!  'Testnofoma' runs a number of tests on the functions in this package;
#!  the argument <A>lev</A> is a positive integer specifying the InfoLevel.
DeclareGlobalFunction("Testnofoma");

#! @Section Further documentation
#! The above functions, as well as a number of further auxiliary functions, 
#! are all contained and defined in the file 'pgk/nofoma-1.0/gap/nofoma.gi'; 
#! in that file, you can also find further inline documentation for the 
#! auxiliary functions.

