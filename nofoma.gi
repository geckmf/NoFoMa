#########################################################################
##
#A  nofoma.gi                                                Meinolf Geck
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

InstallGlobalFunction(IInofoma, function(arg)
  if InfoLevel(Infonofoma)>0 then
    CallFuncList(Print, arg);
  fi;
end);

InstallGlobalFunction(nfmCoeffsPol, function(p) 
  return CoefficientsOfUnivariatePolynomial(p);
end);

InstallGlobalFunction(nfmPolCoeffs, function(coeffs)
  return UnivariatePolynomialByCoefficients(FamilyObj(coeffs[1]),coeffs,1);
end);

# we want that a gcd of polynomials is always monic

InstallGlobalFunction(nfmGcd, function(f,g)
  local d,c;
  d:=Gcd(f,g);
  c:=nfmCoeffsPol(d);
  if c[Length(c)]<>c[1]^0 then
    return c[Length(c)]^(-1)*d;
  else
    return d;
  fi;
end);

InstallGlobalFunction(nfmLcm, function(f,g)
  local d,c;
  d:=Lcm(f,g);
  c:=nfmCoeffsPol(d);
  if c[Length(c)]<>c[1]^0 then
    return c[Length(c)]^(-1)*d;
  else
    return d;
  fi;
end);

##########################################################################
##
#F  GcdCoprimeSplit( <a>, <b> ) . . . . . . . coprime factorisation of lcm
##
##  'GcdCoprimeSplit' computes a divisor <a1> of the polynomial <a>  and a 
##  divisor <b1> of the polynomial <b> such that <a1> and <b1> are coprime 
##  and the lcm of <a>, <b> is <a1>*<b1>.  This is based on Lemma 5 in 
##
##  K. Bongartz,  A direct approach to the rational normal form,  preprint
##  available at arXiv:1410.1683.
## 
##  (Note that it does not use the prime factorisation of polynomials  but 
##  only gcd computations.)  
##  
##  Example:  
##    gap> a:=x^2*(x-1)^3*(x-2)*(x-3);
##    x^7-8*x^6+24*x^5-34*x^4+23*x^3-6*x^2
##    gap> b:=x^2*(x-1)^2*(x-2)^4*(x-4);
##    x^9-14*x^8+81*x^7-252*x^6+456*x^5-480*x^4+272*x^3-64*x^2
##    gap> GcdCoprimeSplit(a,b);
##    [ x^5-4*x^4+5*x^3-2*x^2,                      # the (monic) gcd
##      x^4-6*x^3+12*x^2-10*x+3,                    # a1
##      x^7-12*x^6+56*x^5-128*x^4+144*x^3-64*x^2 ]  # b1
##  
InstallGlobalFunction(GcdCoprimeSplit,function(a,b)
  local d,tb,bb;
  d:=nfmGcd(a,b);
  if Degree(d)=0 then 
    return [d,a,b];
  fi;
  if Degree(b)<=Degree(a) then 
    if Degree(d)=Degree(b) then
      return [b,a,b^0];
    else
      tb:=Quotient(b,d);
      bb:=nfmGcd(tb^Degree(d),d);
      return [d,Quotient(a,bb),tb*bb];
    fi;
  else
    return GcdCoprimeSplit(b,a){[1,3,2]};
  fi;
end);

##########################################################################
##
#F  PolynomialToMatVec( <A>, <pol>, <v> ) . . apply polynomial to a matrix
##  . . . . . . . . . . . . . . . . . . . . . . . . . and then to a vector
##
##  'PolynomialToMatVec' returns  the row vector  obtained  by multiplying 
##  the row vector <v> with the matrix <pol>(<A>), where <pol> is the list 
##  of coefficients of a polynomial.
##
##  Example:
##     gap> A:=([ [ 0, 1, 0, 1 ],
##     gap>       [ 0, 0, 0, 0 ],
##     gap>       [ 0, 1, 0, 1 ],
##     gap>       [ 1, 1, 1, 1 ] ]);;
##     gap> f:=x^6-6*x^5+12*x^4-10*x^3+3*x^2;;
##     gap> v:=[ 1, 1, 1, 1];;
##     gap> l:=nfmCoeffsPol(f);
##     gap> [ 0, 0, 3, -10, 12, -6, 1 ]
##     gap> PolynomialToMat(A,last,v);
##     [ 8, -16, 8, -16 ]
##
InstallGlobalFunction(PolynomialToMatVec,function(A,pol,v)
  local n,v1,i;
  n:=Length(pol);
  v1:=ShallowCopy(pol[n]*v);
  for i in Reversed([1..n-1]) do
    v1:=v1*A;
    if pol[i]<>0*pol[i] then 
      AddRowVector(v1,v,pol[i]);
    fi;
  od;
  return v1;
end);

InstallGlobalFunction(PolynomialToMat,function(A,pol)
  local A1,idm,n,i;
  idm:=A^0;
  n:=Length(pol);
  A1:=pol[n]*idm;
  for i in Reversed([1..n-1]) do
    A1:=A1*A;
    if pol[i]<>0*pol[i] then 
      A1:=A1+pol[i]*idm;
    fi;
  od;
  return A1;
end);

##########################################################################
##
#F  LcmMaximalVectorMat( <A>, <v1>, <v2>, <pol1>, <pol2> ) . . compute lcm
##  . . .  . . . . . . of two minimal polynomials and corresponding vector
##
##  'LcmPolynomialToMatVec' returns,  given  a matrix  <A>,  vectors <v1>,
##  <v2> with minimal polynomials <pol1>, <pol2>,  a new pair [<v>,<pol>],  
##  where <v> has minimal polynomial <pol>, and <pol> is the least common
##  multiple of <pol1> and <pol2>.  
##  This crucially relies on  'GcdCoprimeSplit' to avoid  factorisation of 
##  polynomials.
##
InstallGlobalFunction(LcmMaximalVectorMat,function(A,v1,v2,pol1,pol2)
  local d,v;
  if QuotientRemainder(pol1,pol2)=0*pol1 then 
    return [v1,pol1];
  elif QuotientRemainder(pol2,pol1)=0*pol2 then 
    return [v2,pol2];
  else
    d:=GcdCoprimeSplit(pol1,pol2);
    if Degree(d[1])=0 then
      return [v1+v2,pol1*pol2];
    else
      v:=PolynomialToMatVec(A,nfmCoeffsPol(Quotient(pol1,d[2])),v1)+
             PolynomialToMatVec(A,nfmCoeffsPol(Quotient(pol2,d[3])),v2);
      return [v,d[2]*d[3]];
    fi;
  fi;
end);

##########################################################################
##
#F  SpinMatVector( <A>, <v> ) . . . . . .  spin up a vector under a matrix 
##
##  'SpinMatVector' computes  the  smallest subspace containing the vector  
##  <v>  and invariant under the matrix  <A>.  The  output is a quadruple.  
##  The first component contains a  basis in row echelon form,  the second 
##  the  matrix  with  rows v, Av, A^2v, ..., A^(d-1)v, the third  one the 
##  coefficients of the minimal polynomial of <v>  (of degree d),  and the
##  last one the positions of the pivots of the first component.
## 
##  Examples:
##     gap>  A:=[[2,0,0],[0,-1,0],[0,0,1]];
##     gap>  v:=[1,1,0];
##     gap>  SpinMatVector(A,v);
##     [ [ [ 1, 0, 0 ], [ 0, 1, 0 ] ], 
##       [ [ 1, 1, 0 ], [ 2, -1, 0 ] ], 
##       [ -2, -1, 1 ], [ 1, 2 ] ]    So v has minimal polynomial x^2-x-2.
##     gap>  SpinMatVector(A,[1,1,1]);
##     [ [ [ 1, 0, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], 
##       [ [ 1, 1, 1 ], [ 2, -1, 1 ], [ 4, 1, 1 ] ], 
##       [ 2, -1, -2, 1 ], [ 1, 2, 3 ] ]  minimal polynomial x^3-2x^2-x+2.
##
# this version does not compute the minimal polynomial, only the subspace;
# here, the last four arguments can be empty lists.

InstallGlobalFunction(SpinMatVector1,function(A,v,bahn1,bahn,piv,spiv)
  local d,one,zero,i,j,v1,nv,nv1,koeff,weiter;
  one:=v[1]^0;
  zero:=0*v[1];
  i:=PositionNonZero(v);
  if i>Length(v) then
    Error("# zero vector");
  fi;
  Add(piv,i);
  AddSet(spiv,i);
  Add(bahn,v);
  v1:=ShallowCopy(v);
  MultVector(v1,Inverse(v[i]));
  Add(bahn1,v1);
  d:=Length(bahn1);
  weiter:=true;
  while weiter do 
    nv1:=bahn[Length(bahn)]*A;
    nv:=ShallowCopy(nv1);
    for j in [1..d] do 
      koeff:=-nv[piv[j]];
      if koeff<>zero then 
        AddRowVector(nv,bahn1[j],koeff);
      fi;
    od;
    i:=PositionNonZero(nv);
    if i>Length(nv) then 
      weiter:=false;
    else
      Add(piv,i);
      AddSet(spiv,i);
      if nv[i]=one then 
        Add(bahn1,nv);
      else
        MultVector(nv,Inverse(nv[i]));
        Add(bahn1,nv);
      fi;
      Add(bahn,nv1);
      d:=d+1;
    fi;
  od;
  ConvertToMatrixRepNC(bahn);
  ConvertToMatrixRepNC(bahn1);
  return [bahn1,bahn,nv1,piv,spiv];
end);

InstallGlobalFunction(SpinMatVector,function(mat,vec)
  local sp,minpol;
  sp:=SpinMatVector1(mat,vec,[],[],[],[]); 
  minpol:=-SolutionMat(sp[2],sp[3]);
  Add(minpol,minpol[1]^0);
  return [sp[1],sp[2],minpol,sp[4]];
end);

##########################################################################
##
#F  CyclicChainMat( <A> ) . . . . . . . compute complete chain of relative 
##  . . . . . . . . . . . . cyclic subspaces (with additional information)
##
##  'CyclicChainMat' repeatedly applies 'SpinMatVector1' (relative version
##  of 'SpinMatVector') to compute a chain of cyclic subspaces. The output 
##  is a triple  [B,C,svec]  where C is such that  C*<A>*C^-1  has a block 
##  triangular shape with companian matrices along the diagonal), B is the
##  row echelon form of C and svec is the list of indices where the blocks 
##  begin.
##
##  Example:
##   gap> A:=[ [ 0, 1, 0, 1 ],
##   gap>      [ 0, 0, 1, 0 ],
##   gap>      [ 0, 1, 0, 1 ],
##   gap>      [ 1, 1, 1, 1 ] ]);;
##   gap> sp:=CyclicChainMat(A);
##   [ [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 1 ], [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ] ], 
##     [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 1 ], [ 1, 1, 2, 1 ], [ 0, 0, 0, 1 ] ], 
##     [ 1, 4, 5 ] ]
##   gap> PrintArray(sp[2]*A*sp[2]^-1);
##   [ [    0,    1,    0,    0 ],     There are 2 diagonal blocks, 
##     [    0,    0,    1,    0 ],     one (size 3x3) starting at index 1,
##     [    0,    3,    1,    0 ],     one (size 1x1) starting at index 4.
##     [  1/2,  1/2,  1/2,    0 ] ]
##
InstallGlobalFunction(CyclicChainMat,function(mat)
  local A,k,v,chain,j,idm,sp,one,svec,l;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  one:=A[1][1]^0;
  idm:=IdentityMat(Length(A),k);
  if IsLowerTriangularMat(A) then 
    return [idm,idm,[1..Length(A)+1],[1..Length(A)]];
  fi;
  sp:=SpinMatVector1(A,idm[1],[],[],[],[]);
  svec:=[1,Length(sp[1])+1];
  j:=1;
  while Length(sp[1])<Length(A) do
    while j in sp[5] do
      j:=j+1;
    od;
    sp:=SpinMatVector1(A,idm[j],sp[1],sp[2],sp[4],sp[5]);
    Add(svec,Length(sp[1])+1);
  od;
  return [sp[1],sp[2],svec];
end);

# M=sp[2]*A*sp[2]^-1
InstallGlobalFunction(nfmRelMinPols,function(M,svec)
  local i,l,rpol,one;
  one:=M[1][1]^0;
  rpol:=[];
  for i in [1..Length(svec)-1] do
    l:=ShallowCopy(-M[svec[i+1]-1]{[svec[i]..svec[i+1]-1]});
    Add(l,one);
    Add(rpol,nfmPolCoeffs(l));
  od;
  return rpol;
end);
  
# svec = indices where the blocks start.

##########################################################################
##
#F  CharPolyMat( <A> ) . . . . . .  computes the characteristic polynomial 
#F  MinPolyMat( <A> )  . . . . . . . . . . computes the minimal polynomial 
##  
##  'CharPolyMat' returns the characteristic polynomial of the matrix <A>, 
##  using a chain of cyclic subspaces (see 'CyclicChainMat'); 
##  'MinPolyMat' returns te minimal polynomial.  
##  
##  Example:
##     gap> CharPolyMat([ [ 0, 1, 0, 1 ],
##     gap>               [ 0, 0, 0, 0 ],
##     gap>               [ 0, 1, 0, 1 ],
##     gap>               [ 1, 1, 1, 1 ] ]);
##     x^4-x^3-2*x^2
##  
# This is OrdPoly from Neunhoeffer-Praeger 
InstallGlobalFunction(nfmOrderPolM,function(M,svec,rpols,z,v)
  local i,f,v1,h,g,l;
  f:=[];
  v1:=ShallowCopy(v);
  for i in Reversed([1..z]) do
    l:=v1{[svec[i]..svec[i+1]-1]};
    if l<>0*l then 
      if Degree(rpols[i])=1 then
        g:=rpols[i];
      else
        h:=nfmPolCoeffs(l);
        if Degree(h)=0 then 
          g:=rpols[i];
        else
          g:=Quotient(rpols[i],nfmGcd(rpols[i],h));
        fi;
      fi;
      Add(f,g);
      if i>1 then
        v1:=PolynomialToMatVec(M,nfmCoeffsPol(g),v1);
      fi;
    fi;
  od;
  return Product(f);
end);

# my version of the Neunhoeffer-Praeger algorithm
# if the degree of order poly is small and number of blocks in cyclic 
# chain is large, then check directly if order poly is already the
# minimal polynomial
InstallGlobalFunction(MinPolyMat,function(mat)
  local A,M,k,idm,sp,z,c,i,l,f,f1,v1,rpols,svec,one;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  idm:=IdentityMat(Length(A),k);
  if IsDiagonalMat(A) then       # first deal with diagonal matrix
    one:=A[1][1]^0;
    if ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
      f:=nfmPolCoeffs([-A[1][1],one]);
    else
      l:=Set(List([1..Length(A)],i->A[i][i]));
      f:=nfmPolCoeffs([-l[1],one]);
      for i in [2..Length(l)] do
        f:=nfmPolCoeffs([-l[i],one])*f;
      od;
    fi;
    IInofoma("#I Degree of minimal polynomial is ",Degree(f)," \n");
    return f;
  fi;
  IInofoma("#I Chain complete with \c");
  sp:=CyclicChainMat(A);
  svec:=sp[3];
  if Length(svec)=2 then 
    IInofoma("1 subspace \c");
  else
    IInofoma(Length(svec)-1, " subspaces \c");
  fi;
  M:=sp[2]*A*sp[2]^-1;
  IInofoma(".\c");
  rpols:=nfmRelMinPols(M,svec);
  f:=rpols[1];
  for z in [2..Length(svec)-1] do 
    if Degree(f)^3>Length(svec) or
         PolynomialToMatVec(M,nfmCoeffsPol(f),idm[svec[z]])<>0*idm[1] then 
      f1:=nfmOrderPolM(M,svec,rpols,z,idm[svec[z]]);
      if QuotientRemainder(f,f1)[2]<>0*f1 then 
        IInofoma(".\c");
        f:=Lcm(f,f1);
      fi;
    fi;
  od;
  IInofoma(" degree = ",Degree(f),"\n");
  c:=CoefficientsOfUnivariatePolynomial(f);
  if c[Length(c)]<>c[1]^0 then
    return c[Length(c)]^(-1)*f;
  else
    return f;
  fi;
end); 

##########################################################################
##
#F  MaximalVectorMat( <A> ) . . . . . . . . . . . . compute maximal vector
##
##  'MaximalVectorMat'  returns a maximal vector of the matrix  <A>,  that 
##  is, a vector whose minimal polynomial is that of <A>.  This is done by
##  repeatedly spinning up vectors until a maximal one is found. 
##
##  Example:
##   gap> A:=[ [ 0, 1, 0, 1 ],
##   gap>      [ 0, 0, 0, 0 ],
##   gap>      [ 0, 1, 0, 1 ],
##   gap>      [ 1, 1, 1, 1 ] ];;
##   MaximalVectorMat(A);
##   #I Degree of minimal polynomial is 3 
##   [ [ 0, 0, 1, 0 ], x_1^3-x_1^2-2*x_1 ]
##   (See also FrobHelp(MinPolyMat);)
##   
InstallGlobalFunction(MaximalVectorMat,function(mat)
  local A,M,k,idm,sp,l,np,i,v1,z,one,f,rpols,svec,lm;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  one:=A[1][1]^0;
  idm:=IdentityMat(Length(A),k);
  if IsDiagonalMat(A) then       # first deal with diagonal matrix
    if ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
      v1:=idm[1];
      np:=nfmPolCoeffs([-A[1][1],one]);
    else
      v1:=ListWithIdenticalEntries(Length(A),one);
      ConvertToVectorRepNC(v1,k);
      l:=Set(List([1..Length(A)],i->A[i][i]));
      np:=nfmPolCoeffs([-l[1],one]);
      for i in [2..Length(l)] do
        np:=nfmPolCoeffs([-l[i],one])*np;
      od;
    fi;
    IInofoma("#I Degree of minimal polynomial is ",Degree(np)," \n");
    return [v1,np];
  fi;
  sp:=CyclicChainMat(A);         # general case: transform to cyclic chain
  M:=sp[2]*A*sp[2]^-1;
  svec:=sp[3];
  rpols:=nfmRelMinPols(M,svec);
  lm:=[idm[1],rpols[1]];
  for z in [2..Length(svec)-1] do 
    if Degree(lm[2])^3>Length(svec) or
         PolynomialToMatVec(M,nfmCoeffsPol(lm[2]),idm[svec[z]])<>0*idm[1] then 
      f:=nfmOrderPolM(M,svec,rpols,z,idm[svec[z]]);
      if QuotientRemainder(lm[2],f)[2]<>0*f then 
        lm:=LcmMaximalVectorMat(M,lm[1],idm[svec[z]],lm[2],f);
      fi;
    fi;
  od;
  #v:=lm[1]*sp[2];
  #if SpinMatVector(A,v)[3]<>nfmCoeffsPol(lm[2]) then
  #  Error("mist");
  #else
  #  Print("youpie ");
  #fi;
  IInofoma("#I Degree of minimal polynomial is ",Degree(lm[2]),"\n");
  return [lm[1]*sp[2],lm[2]];
end); 

##########################################################################
##
#F  JacobMatComplement( <T>, <d> ) . . . . . .  compute Jacob's complement
##  . . . . . . . . . . . . . . . . . . . . . . . . . to a cyclic subspace 
##
##  'JacobMatComplement' modifies an already given  complementary subspace 
##  to the  complementary subspace defined by  Jacob;  concretely, this is 
##  realized by assuming that  <T>  is a matrix in block triangular shape, 
##  where the upper left diagonal block is a companion matrix (as returned 
##  by 'RatFormStep1'; the variable <d> gives the size of that block.  
##  (If <T> gives a  maximal cyclic subspace,  then  Jacob's complement is  
##  also  <T>-invariant;  but even if not,  it appears  to be  very useful 
##  because it produces many zeroes.)
##
InstallGlobalFunction(JacobMatComplement,function(T,d)
  local base,null,i,ii,j,k,F,tT;
  k:=DefaultFieldOfMatrix(T);
  base:=IdentityMat(Length(T),k);
  null:=0*base[1][1];
  tT:=TransposedMat(T); 
  F:=[base[d]];
  for i in [2..d] do 
    Add(F,F[i-1]*tT);
  od;
  ConvertToMatrixRepNC(F);
  #TriangulizeMat(F);
  for i in [1..d] do 
    ii:=d+1-i;
    for j in [i+1..d] do 
      if F[j][ii]<>null then
        AddRowVector(F[j],F[i],-F[j][ii]);
      fi;
    od;
  od;
  for i in [d+1..Length(T)] do
    for j in [1..d] do 
      base[i][j]:=-F[d+1-j][i];
    od;
  od;
  ConvertToMatrixRepNC(base);
  return base;
end);

InstallGlobalFunction(BuildBlockDiagonalMat,function(A,B)
  local d,neu,i,n,k,zero,row;
  k:=DefaultFieldOfMatrix(B);
  d:=Length(A);
  n:=d+Length(B);
  zero:=Zero(k);
  row:=ListWithIdenticalEntries(n,zero);
  ConvertToVectorRepNC(row,k);
  neu:=[];
  for i in [1..n] do 
    neu[i]:=ShallowCopy(row);
  od;
  neu{[1..d]}{[1..d]}:=A;
  neu{[d+1..n]}{[d+1..n]}:=B;
  ConvertToMatrixRepNC(neu);
  return neu;
end);

InstallGlobalFunction(BuildBlockDiagonalMat1,function(d,B)
  local neu,n,k;
  k:=DefaultFieldOfMatrix(B);
  n:=d+Length(B);
  neu:=IdentityMat(n,k);
  neu{[d+1..n]}{[d+1..n]}:=B;
  ConvertToMatrixRepNC(neu);
  return neu;
end);

InstallGlobalFunction(RatFormStep1,function(A,v)
  local A1,sp,t,i,k,d,idm,minp;
  k:=DefaultFieldOfMatrix(A);
  idm:=IdentityMat(Length(A),k);
  sp:=SpinMatVector1(A,v,[],[],[],[]);
  t:=sp[2];
  d:=Length(t);
  Append(t,idm{Difference([1..Length(A)],sp[5])});
  ConvertToMatrixRepNC(t);
  A1:=t*A*t^(-1);
  minp:=-ShallowCopy(A1[d]{[1..d]});
  Add(minp,minp[1]^0);
  return [A1,t,minp];
end);

InstallGlobalFunction(RatFormStep1J,function(A,v)
  local A1,sp,t,i,j,k,d,idm,minp;
  k:=DefaultFieldOfMatrix(A);
  idm:=IdentityMat(Length(A),k);
  sp:=SpinMatVector1(A,v,[],[],[],[]);
  t:=sp[2];
  d:=Length(t);
  Append(t,idm{Difference([1..Length(A)],sp[5])});
  ConvertToMatrixRepNC(t);
  A1:=t*A*t^(-1);
  minp:=-ShallowCopy(A1[d]{[1..d]});
  Add(minp,minp[1]^0);
  j:=JacobMatComplement(A1,Length(minp)-1);
  #return [j*A1*j^-1,j*t,minp];
  return [A1{[d+1..Length(A1)]}{[d+1..Length(A1)]},j*t,minp];
end);

InstallGlobalFunction(nfmCompanionMat,function(f)
  local n,i,mat;
  n:=Length(f)-1;
  mat:=(0*f[1])*IdentityMat(n);
  for i in [1..n-1] do 
    mat[i+1][i]:=f[1]^0;
    mat[i][n]:=-f[i];
  od;
  mat[n][n]:=-f[n];
  return mat;
end);

InstallGlobalFunction(nfmCompanionMat1,function(f)
  local n,i,mat;
  n:=Length(f)-1;
  mat:=(0*f[1])*IdentityMat(n);
  for i in [1..n-1] do 
    mat[i][i+1]:=f[1]^0;
    mat[n][i]:=-f[i];
  od;
  mat[n][n]:=-f[n];
  return mat;
end);

InstallGlobalFunction(CreateNormalForm,function(plist)
  local A,l,r,i;
  r:=Length(plist);
  l:=[1];
  for i in [1..r] do
    l[i+1]:=l[i]+Degree(plist[i]);
  od;
  A:=NullMat(l[r+1]-1,l[r+1]-1,nfmCoeffsPol(plist[1])[1]);
  for i in [1..r] do
    A{[l[i]..l[i+1]-1]}{[l[i]..l[i+1]-1]}:=
              TransposedMat(nfmCompanionMat(nfmCoeffsPol(plist[i])));
  od;
  return A;
end);
  
##########################################################################
##
#F  FrobeniusNormalForm( <A> ) . . . . compute the rational canonical form
##
##  'FrobeniusNormalForm' returns the rational canonical form  of a matrix 
##  <A> and an invertible matrix P  performing the base change  (PAP^(-1)=
##  normal). It is first checked if <A> is zero or a scalar matrix,  where 
##  the result is obvious.  Then  the function determines a maximal vector
##  and its minimal polynomial; after that, a recursion is applied. 
##
##  Example: 
##     gap> mat:=[ [ 0, 1, 0, 1 ], 
##                 [ 0, 0, 0, 0 ],
##                 [ 0, 1, 0, 1 ], 
##                 [ 1, 1, 1, 1 ] ]);;
##     gap> f:=FrobeniusNormalForm(mat);
##     #I Degree of minimal polynomial is 3 (2,)
##     [ [ x_1^3-x_1^2-2*x_1, x_1 ], 
##     [ [ 0, 0, 1, 0 ], [ 0, 1, 0, 1 ], [ 1, 1, 1, 1 ], [ 0, -1, 0, 0 ] ], 
##     [ 1, 4 ] ]
##     gap> PrintArray(f[2]*mat*f[2]^-1);
##     [ [  0,  1,  0,  0 ],        This is the Frobenius normal form;
##       [  0,  0,  1,  0 ],        there are 2 diagonal blocks, 
##       [  0,  2,  1,  0 ],        one of size 3 and one of size 1;
##       [  0,  0,  0,  0 ] ]       f[2]=base change matrix
##  
InstallGlobalFunction(FrobeniusNormalForm,function(mat)
  local A,P,invf,i,k,mv,step1,rest,d,piv;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if IsDiagonalMat(A) and ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
    mv:=nfmPolCoeffs([-A[1][1],A[1][1]^0]);
    return [ListWithIdenticalEntries(Length(A),mv),A^0,[1..Length(A)]];
  fi;
  mv:=MaximalVectorMat(A);
  invf:=[mv[2]];
  d:=Degree(mv[2]);
  if d=Length(A) then      # cyclic space: only one companion block
    step1:=[mv[1]];        # create base change
    for i in [2..d] do
      Add(step1,step1[i-1]*A);
    od;
    ConvertToMatrixRepNC(step1);
    return [invf,step1,[1]];
  else
    step1:=RatFormStep1J(A,mv[1]);       # compute Jacob complement
    piv:=[1];
    rest:=FrobeniusNormalForm(step1[1]);
    P:=BuildBlockDiagonalMat1(d,rest[2]);
    Append(invf,rest[1]);
    for i in rest[3] do 
      Add(piv,i+d);
    od;
    return [invf,P*step1[2],piv];
  fi;
end);

InstallGlobalFunction(FrobeniusNormalForm1,function(mat)
  local A,A1,A2,P,i,k,step1,rest,d,piv;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then 
    #Print("#I Zero matrix\n");
    return [A,A^0,List([1..Length(A)],i->i)];
  fi;
  if IsDiagonalMat(A) and ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
    #Print("#I Scalar matrix \n");
    return [A,A^0,List([1..Length(A)],i->i)];
  fi;
  step1:=RatFormStep1J(A,MaximalVectorMat(A)[1]);
  A1:=step1[1];
  d:=Length(step1[3])-1;
  return ImmutableMatrix(k,A1);
end);

##########################################################################
##
#F  InvariantFactorsMat( <A> ) . . . . . . . compute the invariant factors 
##
##  'InvariantFactorsMat' returns the invariant factors of the matrix <A>,
##  i.e.,  the minimal polynomials of the  diagonal blocks in the rational 
##  canonical form  of <A>. Thus, 'InvariantFactorsMat' also specifies the
##  rational canonical form of <A>, but without computing the base change.
##
InstallGlobalFunction(InvariantFactorsMat,function(mat)
  local A,A1,i,d,np,k,f,n,p;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  np:=MaximalVectorMat(A);
  d:=Degree(np[2]);
  f:=[np[2]];
  if d=n then 
    return f;
  elif d=1 then 
    return ListWithIdenticalEntries(n,np[2]);
  else
    A1:=RatFormStep1(A,np[1])[1];
    Append(f,InvariantFactorsMat(A1{[d+1..n]}{[d+1..n]}));
    return f;
  fi;
end);

# F=output of FrobeniusNormalForm
InstallGlobalFunction(CheckFrobForm,function(A,F)
  local P,k,i,nf;
  nf:=CreateNormalForm(F[1]);
  k:=DefaultFieldOfMatrix(A);
  P:=F[2];
  if P*A*P^(-1)<>nf then 
    Error("base change not ok!");
  fi;
  for i in [1..Length(F[1])-1] do 
    if QuotientRemainder(F[1][i],F[1][i+1])[2]<>0*F[1][i] then 
      Error("divisibility not ok!");
    fi;
  od;
  return true;
end);
  
## Now Jordan-Chevalley decomposition

InstallGlobalFunction(nfmFrobInv,function(K1,p,x)
  local i;
  i:=1;
  while K1[i]^p<>x do
    i:=i+1;
  od;
  return K1[i];
end);

InstallGlobalFunction(SquareFreePol,function(f)
  local K,K1,d,n,i,p,df,f1,g,g1,g2,cf;
  n:=Degree(f);
  if n=1 then 
    return [f,1];
  else
    df:=Derivative(f);
    if df<>0*df then 
      f1:=nfmGcd(f,df);
      if Degree(f1)=0 then
        return [f,1];
      else
        g1:=SquareFreePol(f1);
        g2:=SquareFreePol(Quotient(f,f1));
        return [nfmLcm(g1[1],g2[1]),g1[2]+g2[2]]; 
      fi;
    else
      cf:=nfmCoeffsPol(f);
      K:=DefaultField(cf[1]);
      K1:=Elements(K);
      p:=Characteristic(K);
      g:=SquareFreePol(nfmPolCoeffs(List([0..n/p],
                             i->nfmFrobInv(K1,p,cf[p*i+1]))));
      return [g[1],p*g[2]];
    fi;
  fi;
end);

##########################################################################
##
#F  JordanChevalleyDecMat( <A>, <f> ) . . . . compute the Jordan-Chevalley
#F  JordanChevalleyDecMatF( <A> ) . . . . . . .  decomposition of a matrix
##
##  'JordanChevalleyDecMat'' returns the unique pair of matrices D,N where  
##  D is diagonalisable over some extension field of the  default field of 
##  the matrix <A>  and  N is a nilpotent matrix such that  <A>=D + N  and 
##  DN=ND;  the argument <f> is a polynomial such that  f(A)=0  (e.g., the 
##  the minimal polynomial of <A>). 
##
##  'JordanChevalleyDecMatF'  first computes the Frobenius normal form and
##  then applies 'JordanChevalleyDecMat' to each diagonal block.
##
##  Example:
##     gap> A:=[ [ 0, 0, 0 ], [ 1, 0, -1 ], [ 0, 1, -2 ] ];
##     gap> f:=MinimalPolynomials(A);
##     x_1^3+2*x_1^2+x_1
##     jc:=JordanChevalleyDecMat(A,f);
##     [ [ [ 0, 0, 0 ], [ 2, -1, 0 ], [ 1, 0, -1 ] ], 
##       [ [ 0, 0, 0 ], [ -1, 1, -1 ], [ -1, 1, -1 ] ] ]
##     gap> MinimalPolynomial(j[1]);
##     x_1^2+x_1
##     gap> MinimalPolynomial(j[2]);
##     x_1^2
##
##  '
##  The algorithm is based on the preprint at arXiv:2205.05432.
##
InstallGlobalFunction(JordanChevalleyDecMat,function(mat,f)
  local A,Ak,k0,gg,g,tg;
  A:=ImmutableMatrix(DefaultFieldOfMatrix(mat),mat);
  gg:=SquareFreePol(f);
  g:=nfmCoeffsPol(gg[1]);
  tg:=nfmCoeffsPol(GcdRepresentation(Derivative(gg[1]),gg[1])[1]);
  k0:=0;
  Ak:=A;
  IInofoma("#I Iterations (m=",gg[2],"): \c");
  while 2^k0<gg[2] do 
    Ak:=Ak-PolynomialToMat(Ak,g)*PolynomialToMat(Ak,tg);
    k0:=k0+1;
    IInofoma(".\c");
  od;
  IInofoma("\n");
  return [Ak,A-Ak];
end);

InstallGlobalFunction(JordanChevalleyDecMatF,function(mat)
  local f,jc,p,N,D;
  f:=FrobeniusNormalForm(mat);
  IInofoma("#I Frobenius normal form complete\n");
  Add(f[3],Length(mat)+1);
  jc:=List(f[1],p->JordanChevalleyDecMat(nfmCompanionMat1(nfmCoeffsPol(p)),p));
  N:=0*f[2];
  D:=0*f[2];
  for p in [1..Length(f[1])] do 
    D{[f[3][p]..f[3][p+1]-1]}{[f[3][p]..f[3][p+1]-1]}:=jc[p][1];
    N{[f[3][p]..f[3][p+1]-1]}{[f[3][p]..f[3][p+1]-1]}:=jc[p][2];
  od;
  return [f[2]^-1*D*f[2],f[2]^-1*N*f[2]];
end);
  
InstallGlobalFunction(CheckJordanChev,function(mat,jc)
  local m;
  m:=MinPolyMat(jc[1]);
  return [nfmGcd(m,Derivative(m)),MinPolyMat(jc[2])];
end);

InstallGlobalFunction(Testnofoma,function(lev)
  local test,diagmat,bev,steel,ddd,mat1;
  test:=function(a1)
    local a,aa;
    a:=CyclicChainMat(a1);
    a:=MinPolyMat(a1);
    a:=InvariantFactorsMat(a1);
    a:=FrobeniusNormalForm(a1);
    if CheckFrobForm(a1,a)=false
      then Error(" --> tests not OK !\n");
    fi;
    if CheckJordanChev(a1,JordanChevalleyDecMat(a1,MinPolyMat(a1)))=false
      then Error(" --> tests not OK !\n");
    fi;
  end;
  diagmat:=function(l)
    local m,i;
    m:=l[1]*IdentityMat(Length(l));
    for i in [2..Length(l)] do
      m[i][i]:=l[i];
    od;
   return m;
  end;
  mat1:=function(mat)
    local a,a1,b,i;
    a1:=TransposedMat(Concatenation(mat,mat));
    a:=[];
    for i in [1..Length(a1)-1] do
      Add(a,a1[i]);
    od;
    Add(a,0*a1[1]);
    b:=TransposedMat(Concatenation(TransposedMat(mat),TransposedMat(mat)));
    return Concatenation(a,b);
  end;
  SetInfoLevel(Infonofoma,lev);
  bev:=TransposedMat(
  [[2,0,0,0,0,0,0], [2,4,1,-1,-7,-2,-1], [0,0,1,0,0,0,0], [1,0,0,1,0,0,0],
  [0,0,0,0,1,0,0], [2,1,1,-1,-5,1,-1], [1,0,1,0,0,0,1]]);
  steel:=
  [[-23,19,-9,-75,34,9,56,15,-34,-9], [-2,2,-1,-6,3,1,4,2,-3,0],
  [4,-4,3,10,-5,-1,-6,-4,5,1], [-2,2,-1,-5,3,1,3,2,-3,0],
  [0,0,0,0,2,0,0,0,0,0], [12,-12,6,33,-18,-4,-18,-12,18,0],
  [-1,-3,0,2,1,0,1,1,2,1], [-26,22,-10,-83,36,10,61,18,-39,-10],
  [-1,-3,0,1,1,0,2,1,2,0], [8,-12,4,27,-12,-4,-12,-7,15,0]];
  ddd:=diagmat([1,2,-1,0,4,3,3,4,5,6,7,-1,5,4,0,0,3,2,1]);
  test(steel); test(bev); test(ddd);
  test(Z(4)^0*steel); test(Z(4)^0*bev); test(Z(4)^0*ddd);
  test(mat1(steel)); test(Z(29)*mat1(steel));
  test(RandomMat(15,15,Integers));
  test(RandomMat(20,20,GF(49)));
  Print("\n--> tests OK !\n\n");
end);

FrobHelp:=function(f)
  local i,l,s1,s2,s2a,s3,s4,s5,s5a,s5b,s6,s7,s7a,s8,s8a,s8b,s9,s9a,s10,s11,
        s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,
        s28,s29,s30;
  if f=MaximalVectorMat then 
s1:="";
s3:="MaximalVectorMat( <A> ) . . . . . . . . . . . . compute maximal vector";
s4:="'MaximalVectorMat' returns a maximal vector and the minimal polynomial";
s5:="of the matrix  <A>. The algorithm is basically that of Neunhoeffer and";
s6:="Praeger (LMS J. Comput. Math. 11, 2008), but modified so as to produce";
s8:="a maximal vector *along* with the minimal polynomial.";
s12:="(This is crucial for the determination of the Frobenius normal form.)";
s9:="Also note:  This algorithm does not rely on the prime factorisation of";
s10:="polynomials; hence, it works over any field that is available in GAP.";
s13:="Example:  ";
s14:=" gap> A:=[ [ 0, 1, 0, 1 ],";
s15:=" gap>      [ 0, 0, 0, 0 ],";
s16:=" gap>      [ 0, 1, 0, 1 ],";
s17:=" gap>      [ 1, 1, 1, 1 ] ];;";
s18:=" MaximalVectorMat(A);";
s19:=" #I Degree of minimal polynomial is 3";
s20:=" [ [ 0, 0, 1, 0 ], x_1^3-x_1^2-2*x_1 ]";
s21:="";
s22:="('NPMaximalVector' from the previous release has become obsolete.)";
    l:=[s1,s3,s1,s4,s5,s6,s8,s12,s1,s9,s10,s1,s13,s14,s15,s16,s17,s18,
        s19,s20,s21,s22];
    for i in l do Print(i,"\n");od;
  elif f=FrobeniusNormalForm then  
s1:="";
s2:="FrobeniusNormalForm( <A> ) . . . . compute the rational canonical form";
s4:="";
s5:="'FrobeniusNormalForm' returns the rational canonical form  of a matrix";
s6:="<A>, and an invertible matrix P performing the base change  (such that";
s7:="P*<A>*P^(-1) = normal form). The output is a triple with";
s8:="        first component  = list of invariant factors,";
s9:="        second component = base change matrix P,";
s10:="         third component = positions where the various blocks begin.";
s12:="";
s13:="Example:";
s14:="  gap> mat:=[ [ 0, 1, 0, 1 ],";
s15:="              [ 0, 0, 0, 0 ],";
s16:="              [ 0, 1, 0, 1 ],";
s17:="              [ 1, 1, 1, 1 ] ];;";
s18:="  gap> f:=FrobeniusNormalForm(mat);";
s19:="  #I Degree of minimal polynomial is 3";
s20:="  [ [ x_1^3-x_1^2-2*x_1, x_1 ],    #  f[1] = List of invariant factors";
s21:="  [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 1 ], [ 1, 1, 1, 1 ], [ 0, -1, 0, 0 ] ],";
s22:="  [ 1, 4 ] ];        # f[3] = Positions where the various blocks begin";
s23:="  gap> PrintArray(f[2]*mat*f[2]^-1);";
s24:="  [ [  0,  1,  0,  0 ],          #  This is the Frobenius normal form;";
s25:="    [  0,  0,  1,  0 ],          #  there are 2 diagonal blocks, ";
s26:="    [  0,  2,  1,  0 ],          #  one of size 3 and one of size 1;";
s27:="    [  0,  0,  0,  0 ] ]         #  f[2] = base change matrix";
s3:="  (You can also use  'CreateNormalForm(f[1]);' to produce the latter.)";
s28:="";
s30:="('NPFrobeniusNormalForm' from the previous release is now obsolete.)";
    l:=[s1,s2,s4,s5,s6,s7,s8,s9,s10,s12,s13,s14,s15,s16,s17,s18,s19,
        s20,s21,s22,s23,s24,s25,s26,s27,s3,s28,s30];
    for i in l do Print(i,"\n");od;
elif f=SpinMatVector then 
s1:="";
s2:="SpinMatVector( <A>, <v> ) . . . . . .  spin up a vector under a matrix";
s3:="'SpinMatVector' computes  the  smallest subspace containing the vector";
s4:="<v>  and invariant under the matrix  <A>.  The  output is a quadruple.";
s5:="The first component contains a  basis in row echelon form,  the second";
s6:="the  matrix  with  rows v, Av, A^2v, ..., A^(d-1)v, the third  one the";
s7:="coefficients of the minimal polynomial of <v>  (of degree d),  and the";
s8:="last one the positions of the pivots of the first component.";
s9:="";
s10:="Examples:";
s11:="   gap>  A:=[[2,0,0],[0,-1,0],[0,0,1]];";
s12:="   gap>  v:=[1,1,0];";
s13:="   gap>  SpinMatVector(A,v);";
s14:="   [ [ [ 1, 0, 0 ], [ 0, 1, 0 ] ], ";
s15:="     [ [ 1, 1, 0 ], [ 2, -1, 0 ] ], ";
s16:="     [ -2, -1, 1 ], [ 1, 2 ] ]    So v has minimal polynomial x^2-x-2.";
s17:="   gap>  SpinMatVector(A,[1,1,1]);";
s18:="   [ [ [ 1, 0, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], ";
s19:="     [ [ 1, 1, 1 ], [ 2, -1, 1 ], [ 4, 1, 1 ] ], ";
s20:="     [ 2, -1, -2, 1 ], [ 1, 2, 3 ] ]  minimal polynomial x^3-2x^2-x+2.";
    l:=[s1,s2,s1,s3,s4,s5,s6,s7,s8,s9,s11,s12,s13,s14,s15,s16,s17,s18,s19,
        s20,s1];
    for i in l do Print(i,"\n");od;
elif f=JordanChevalleyDecMat or f=JordanChevalleyDecMatF then 
s1:="";
s2:="JordanChevalleyDecMat( <A>, <f> ) . . . . compute the Jordan-Chevalley";
s3:="JordanChevalleyDecMatF( <A> ) . . . . . . .  decomposition of a matrix";
s4:="'JordanChevalleyDecMat' returns the unique pair of matrices D, N where";
s5:="D  is  diagonalisable  over some extension field of the  default field";
s6:="of the matrix <A> and N is a nilpotent matrix  such that <A>=D + N and";
s7:="DN=ND;  the argument  <f> is a polynomial such that  f(A)=0 (e.g., the";
s8:="minimal polynomial of <A>).";
s8a:="'JordanChevalleyDecMatF' first computes the  Frobenius normal form and";
s8b:="then applies 'JordanChevalleyDecMat' to each diagonal block.";
s9:="Example:";
s10:="   gap> A:=[ [ 0, 0, 0 ], [ 1, 0, -1 ], [ 0, 1, -2 ] ];";
s11:="   gap> f:=MinimalPolynomials(A);";
s12:="   x_1^3+2*x_1^2+x_1";
s13:="   jc:=JordanChevalleyDecMat(A,f);";
s14:="   [ [ [ 0, 0, 0 ], [ 2, -1, 0 ], [ 1, 0, -1 ] ],";
s15:="     [ [ 0, 0, 0 ], [ -1, 1, -1 ], [ -1, 1, -1 ] ] ]";
s16:="   gap> MinimalPolynomial(j[1]);";
s17:="   x_1^2+x_1";
s18:="   gap> MinimalPolynomial(j[2])";
s19:="   x_1^2";
s20:="The algorithm is based on the preprint at arXiv:2205.05432.";
    l:=[s1,s2,s3,s1,s4,s5,s6,s7,s8,s1,s8a,s8b,s1,s9,s10,s11,s12,s13,s14,
        s15,s16,s17,s18,s19,s1,s20];
    for i in l do Print(i,"\n");od;
##

elif f=CyclicChainMat then 
s1:="";
s2:="CyclicChainMat( <A> ) . . . . . . . . . . .  chain of cyclic subspaces";
s4:="";
s5:="'CyclicChainMat' repeatedly applies 'SpinMatVector1' (relative version";
s6:="of 'SpinMatVector') to compute a chain of cyclic subspaces. The output";
s7:="is a triple [B,C,svec]  where  C is such that  C*<A>*C^-1  has a block";
s8:="triangular shape with companian matrices along the diagonal), B is the";
s9:="row echelon form of C and svec is the list of indices where the blocks";
s10:="begin.";
s11:="";
s12:="Example:";
s13:="  gap> A:=[ [ 0, 1, 0, 1 ],";
s14:="  gap>      [ 0, 0, 1, 0 ],";
s15:="  gap>      [ 0, 1, 0, 1 ],";
s16:="  gap>      [ 1, 1, 1, 1 ] ]);;";
s17:="  gap> sp:=CyclicChainMat(A);";
s18:="  [ [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 1 ], [ 0, 0, 1, 0 ], [ 0, 0, 0, 1 ] ],";
s19:="    [ [ 1, 0, 0, 0 ], [ 0, 1, 0, 1 ], [ 1, 1, 2, 1 ], [ 0, 0, 0, 1 ] ],";
s20:="    [ 1, 4, 5 ] ]";
s21:="  gap> PrintArray(sp[2]*A*sp[2]^-1);";
s22:="  [ [    0,    1,    0,    0 ],    There are 2 diagonal blocks,";
s23:="    [    0,    0,    1,    0 ],    one (size 3x3) starting at index 1,";
s24:="    [    0,    3,    1,    0 ],    one (size 1x1) starting at index 4.";
s25:="    [  1/2,  1/2,  1/2,    0 ] ]";
    l:=[s1,s2,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,
        s20,s21,s22,s23,s24,s25,s1];
    for i in l do Print(i,"\n");od;
elif f=MinPolyMat then 
s1:="";
s2:="CharPolyMat( <A> ) . . . . . .  computes the characteristic polynomial";
s2a:="MinPolyMat( <A> ) . . . . . . . . . .  computes the minimal polynomial";
s4:="'CharPolyMat' returns the characteristic polynomial of the matrix <A>,";
s5:="using a chain of  relative cyclic subspaces (see 'CyclicChainMat').";
s5a:="'MinPolyMat' returns the minimal polyonial of <A>;  it is essentially";
s3:="the same as 'MaximalVectorMat' (but without a maximal vector).";
s5b:="These are alternatives to the built-in GAP functions.";
s6:="";
s7:="Example:";
s8:="   gap> A:=[ [ 2,  2, 0, 1, 0,  2, 1 ],"; 
s9:="             [ 0,  4, 0, 0, 0,  1, 0 ],";
s10:="             [ 0,  1, 1, 0, 0,  1, 1 ],";
s11:="             [ 0, -1, 0, 1, 0, -1, 0 ],";
s12:="             [ 0, -7, 0, 0, 1, -5, 0 ],";
s13:="             [ 0, -2, 0, 0, 0,  1, 0 ],";
s14:="             [ 0, -1, 0, 0, 0, -1, 1 ] ];;";
s15:="   gap> CharPolyMat(A);";
s16:="   -x^7+11*x^6-50*x^5+122*x^4-173*x^3+143*x^2-64*x+12";
s17:="   gap> MinPolyMat(A);";
s18:="   x^4-7*x^3+17*x^2-17*x+6";
    l:=[s1,s2,s2a,s1,s4,s5,s1,s5a,s3,s1,s5b,s6,s7,s8,s9,s10,s11,s12,
              s13,s14,s15,s16,s17,s18,s1];
    for i in l do Print(i,"\n");od;
elif f=GcdCoprimeSplit then 
s1:="";
s2:="GcdCoprimeSplit( <a>, <b> ) . . . . . . . coprime factorisation of lcm";
s3:="'GcdCoprimeSplit' computes a divisor <a1> of the polynomial <a>  and a ";
s4:="divisor <b1> of the polynomial <b> such that <a1> and <b1> are coprime ";
s5:="and the lcm of <a>, <b> is <a1>*<b1>.  This is based on Lemma 5 in ";
s6:="";
s7:="K.Bongartz,  A direct approach to the rational normal form,";
s8:="preprint available at arXiv:1410.1683.";
s9:="(see also Lemma 4.3 in M.Geck, https://doi.org/10.13001/ela.2020.5055).";
s9a:="";
s10:="(Note that it does not use the prime factorisation of polynomials  but ";
s11:="only gcd computations.)  ";
s12:="";
s13:="Example:  ";
s14:="  gap> a:=x^2*(x-1)^3*(x-2)*(x-3);";
s15:="  x^7-8*x^6+24*x^5-34*x^4+23*x^3-6*x^2";
s16:="  gap> b:=x^2*(x-1)^2*(x-2)^4*(x-4);";
s17:="  x^9-14*x^8+81*x^7-252*x^6+456*x^5-480*x^4+272*x^3-64*x^2";
s18:="  gap> GcdCoprimeSplit(a,b);";
s19:="  [ x^5-4*x^4+5*x^3-2*x^2,                      # the (monic) gcd";
s20:="    x^4-6*x^3+12*x^2-10*x+3,                    # a1";
s21:="    x^7-12*x^6+56*x^5-128*x^4+144*x^3-64*x^2 ]  # b1";
    l:=[s1,s2,s1,s3,s4,s5,s6,s7,s8,s9,s9a,s10,s11,s12,s13,s14,s15,s16,s17,
        s18,s19,s20,s21,s1];
    for i in l do Print(i,"\n");od;
  elif f=RatFormStep1J or f=RatFormStep1 then 
s1:="";
s2:="RatFormStep1J( <A>, <v> ) . . . . . . . . compute cyclic subspaces and";
s3:=". . . . . . . . . . . . . . . . . . . . . . . . . . perform base chain";
s2a:="RatFormStep1Js( <A>, <v> ) . . . strong form with invariant complement";
s4:="";
s5:="'RatFormStep1J' spins up a vector  <v> under a  matrix  <A>,  computes";
s6:="a complementary subspace  (using  Jacob's construction),  and performs"; 
s7:="the base change. The output is a quadruple  [A1,P,pol,str] where A1 is";
s7a:="the new matrix,  P is the base change,  pol is  the minimal polynomial";
s8:="and str is either 'split' or 'not', according to whether the extension";
s9:="is split or not. The second form repeatedly applies 'RatFormStep1J' in";
s10:="order to obtain an invariant complement.";
s11:="Example:";
s12:=" gap> v:=[ 1, 1, 1, 1 ];;";
s13:=" gap> A:=[ [ 0, 1, 0, 1 ],";
s14:=" gap>      [ 0, 0, 1, 0 ],";
s15:=" gap>      [ 0, 1, 0, 1 ],";
s16:=" gap>      [ 1, 1, 1, 1 ] ];;";
s17:=" gap> PrintArray(RatFormStep1J(A,v)[1])";
s18:=" [ [  0,  1,  0,  0 ],    There are 2 diagonal blocks but";
s19:="   [  0,  0,  1,  0 ],    (because of the (4,1)-entry 1)";
s20:="   [  0,  3,  1,  0 ],    the extension is not split.";
s21:="   [  1,  0,  0,  0 ] ]   ";
s22:=" gap> PrintArray(RatFormStep1Js(A,v)[1])";
s23:=" [ [  0,  1,  0,  0 ],    Now we actually see that";
s24:="   [  0,  0,  1,  0 ],    the matrix is cyclic.";
s25:="   [  0,  0,  0,  1 ],    "; 
s26:="   [  0,  0,  3,  1 ] ]   ";
    l:=[s1,s2,s3,s2a,s4,s5,s6,s7,s7a,s8,s9,s10,s1,s11,s12,s13,s14,s15,s16,
                              s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s1];
    for i in l do Print(i,"\n");od;
elif f=InvariantFactorsMat then
s1:="";
s2:="InvariantFactorsMat( <A> ) . . . . . . . compute the invariant factors ";
s4:="'InvariantFactorsMat' returns the invariant factors of the matrix <A>,";
s5:="i.e.,  the minimal polynomials of the  diagonal blocks in the rational ";
s6:="canonical form  of <A>. Thus, 'InvariantFactorsMat' also specifies the";
s7:="rational canonical form of <A>, but without computing the base change.";
s9:="Example:";
s10:="   gap> InvariantFactorsMat([ [ 2,  2, 0, 1, 0,  2, 1 ],";
s11:="                              [ 0,  4, 0, 0, 0,  1, 0 ],";
s12:="                              [ 0,  1, 1, 0, 0,  1, 1 ],";
s13:="                              [ 0, -1, 0, 1, 0, -1, 0 ],";
s14:="                              [ 0, -7, 0, 0, 1, -5, 0 ],";
s15:="                              [ 0, -2, 0, 0, 0,  1, 0 ],";
s16:="                              [ 0, -1, 0, 0, 0, -1, 1 ] ]);";
s17:="   #I Degree of minimal polynomial is 4";
s18:="   #I Degree of minimal polynomial is 2";
s19:="   [ x^4-7*x^3+17*x^2-17*x+6, x^2-3*x+2, x-1 ]";
    l:=[s1,s2,s1,s4,s5,s6,s7,s1,s9,s10,s11,s12,s13,s14,
                                        s15,s16,s17,s18,s19,s1];
    for i in l do Print(i,"\n");od;
  else
   Print("sorry help not available\n"); 
  fi;
end;
