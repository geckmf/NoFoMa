# NoFoMa

This is a package with  GAP4 functions for computing maximal vectors,
minimal polynomials, the rational canonical form (or Frobenius normal 
form)  and also the Jordan-Chevalley  decomposition of a  matrix over 
any field that is available in GAP. 

The algorithms are based on, and a combination of:  
 
 K. Bongartz,  A direct approach to the rational normal form, preprint
                         available at https://arxiv.org/abs/1410.1683.

 M. Neunhoeffer and  C. E. Praeger,  Computing minimal polynomials  of
                    matrices, LMS J. Comput. Math. 11 (2008), 252-279;

 M. Geck,  On Jacob's construction  of  the  rational  canonical form, 
                       Electron. J. Linear Algebra 36 (2020), 177-182;
                                https://doi.org/10.13001/ela.2020.5055

 M. Geck, On the Jordan-Chevalley decomposition of a matrix,  preprint
                        available at https://arXiv.org/abs/2205.05432.

Installing: Inside a GAP session, just say

gap> Read("nofoma.gd");
gap> Read("nofoma.gi");

Or unpack nfm1r0.tar.gz and place the resulting directory  nofoma-1.0 
inside the pkg directory of your local GAP installation. Then you can 
just load the package by

gap> LoadPackage("nofoma");
