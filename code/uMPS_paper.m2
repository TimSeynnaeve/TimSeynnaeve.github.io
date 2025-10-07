--------------------------------------------------
-----The trace parametrization of uMPS(2,2,N)-----
--------------------------------------------------
restart
K=QQ
--The trace algebra for D=d=2 is the polynomial ring in 5 variables
R=K[T_0..T_4]
H = new MutableHashTable;
--H#(i,j,k,...)=trace(A_i*A_j*A_k*...), written in the T_i's
H#{0} = T_0
H#{1} = T_1
H#{0,0} = T_2
H#{0,1} = T_3
H#{1,0} = T_3
H#{1,1} = T_4
--For any 2x2 matrices A,B,C, the following identity holds:
--tr(ABC)+tr(BAC)=tr(A)tr(BC)+tr(B)tr(CA)+tr(C)tr(AB)-tr(A)tr(B)tr(C)
--Furthermore note that if 2 of the matrices A,B,C are equal, then tr(ABC)=tr(BAC). So the above identity allows us to write the trace parametrization of uMPS(2,2,3)
for i in (toList ((set {0,1})^**3/deepSplice)) do {
    i=toList i;
    H#i = ((H#{i#0})*(H#{i#1,i#2})+(H#{i#1})*(H#{i#2,i#0})+(H#{i#2})*(H#{i#0,i#1})-(H#{i#0})*(H#{i#1})*(H#{i#2}))/2
    }

--For N>3 we use the following identity of 2x2 matrices
--2tr(ABCD)=tr(A)(tr(BCD)-tr(B)tr(CD))+tr(B)(tr(CDA)-tr(C)tr(DA))+tr(C)(tr(DAB)-tr(D)tr(AB))+tr(D)(tr(ABC)-tr(A)tr(BC))-tr(AC)tr(BD)+tr(AB)tr(CD)+tr(AD)tr(BC)+tr(A)tr(B)tr(C)tr(D)

for N in {4,5,6} do {
for i in (toList ((set {0,1})^**N/deepSplice)) do {
    i = toList i;
    a={i#0};
    b={i#1};
    c={i#2};
    d=apply(N-3,j->(i#(j+3)));
    H#i = (
	 (H#a)*((H#(b|c|d))-((H#b)*(H#(c|d))))
	+(H#b)*((H#(c|d|a))-((H#c)*(H#(d|a))))
	+(H#c)*((H#(d|a|b))-((H#d)*(H#(a|b))))
	+(H#d)*((H#(a|b|c))-((H#a)*(H#(b|c))))
	-(H#(a|c))*(H#(b|d))
	+(H#(a|b))*(H#(c|d))
	+(H#(a|d))*(H#(b|c))
	+(H#a)*(H#b)*(H#c)*(H#d)
	)/2
};
}
--Now we can write down the maps defining uMPS(2,2,N) for N=4,5,6
P4={{0,0,0,0},{0,0,0,1},{0,0,1,1},{0,1,1,1},{1,1,1,1},{0,1,0,1}}
L4=apply(P4,j->H#j)
S4=K[apply(P4,j->x_j)]
F4=map(R,S4,L4)
KER4 = kernel(F4)

--------------------------------------
-----Defining equations for N=5,6-----
--------------------------------------
--First run the first section "The trace parametrization of uMPS(2,2,N)"
P5={{0,0,0,0,0},{0,0,0,0,1},{0,0,0,1,1},{0,0,1,1,1},{0,1,1,1,1},{1,1,1,1,1},{0,0,1,0,1},{1,1,0,1,0}}
L5=apply(P5,j->H#j)
S5=K[apply(P5,j->x_j)]
F5=map(R,S5,L5)
KER5 = kernel(F5)
degrees mingens KER5
--We find 3 quartics and 27 sextics

P6={{0,0,0,0,0,0},{0,0,0,0,0,1},{0,0,0,0,1,1},{0,0,0,1,1,1},{0,0,1,1,1,1},{0,1,1,1,1,1},{1,1,1,1,1,1},{0,1,0,1,0,0},{1,0,0,1,0,0},{1,0,1,0,1,1},{0,1,1,0,1,1},{1,1,0,0,1,0},{0,0,1,1,0,1},{0,1,0,1,0,1}}
L6=apply(P6,j->H#j)
S6=K[apply(P6,j->x_j)]
F6=map(R,S6,L6)
KER6 = kernel(F6)
degrees mingens KER6
--We find 1 linear form, 6 quadrics, and 17 cubics

--------------------------------------------
-----uMPS(2,2,4) as a constructible set-----
--------------------------------------------
--First run the first section "The trace parametrization of uMPS(2,2,N)"
--This section needs the "TotalImage.m2" package [Harris, Michalek, Sertoz]
--It is available online at https://github.com/coreysharris/TotalImage
loadPackage "TotalImage"
--We make a substitution to make the map homogenous. This doesn't change the image
Rhom=QQ[A,B,C,D,E]
subhom={T_0 =>A, T_1 =>B,T_2 =>(C^2),T_3 =>(D^2),T_4 =>(E^2)}
Hhom = new MutableHashTable;
for i in (toList ((set {0,1})^**4/deepSplice)) do {
    i = toList i;
    Hhom#i=sub(H#i,subhom);
    }
L4hom=apply(P4,j->Hhom#j)

--Ideal defining Y_1
y1={x_{0,0,0,1},x_{0,1,1,1},x_{1,1,1,1},2*x_{0,0,1,1}+x_{0,1,0,1}}
Y1=ideal(y1)
--Ideal defining V(f_{224}) \cap Y_1
X1=radical (Y1+KER4)
--Ideal defining T^{-1}(Y_1)
YY1=radical ideal(apply(y1,el -> sub(el,apply(P4, j->(x_j => Hhom#j)))))
--We compute the image Z1 = T(T^{-1}(Y_1))
Im1=totalImage(L4hom,YY1,Verbose => true)
--We find that Z1 is a closed set, defined by the following ideal
Z1=Im1#0#0
--We compare Z1 and X1
Sy=ring Z1
subyx=apply(6,i->(y_i=>x_(P4#i)))
sub(Z1,subyx)==X1
--Z1 and X1 both define one point in projective space: e_{0,0,0,0}

--Ideal defining Y_2
y2={x_{0,0,0,0},x_{0,1,1,1},x_{1,1,1,1},2*x_{0,0,1,1}+x_{0,1,0,1}}
Y2=ideal(y2)
--Ideal defining V(f_{224}) \cap Y_2
X2=radical (Y2+KER4)
--Ideal defining T^{-1}(Y_2)
YY2=radical ideal(apply(y2,el -> sub(el,apply(P4, j->(x_j => Hhom#j)))))
--We compute the image Z2 = T(T^{-1}(Y_2))
Im2=totalImage(L4hom,YY2,Verbose => true)
--We find that Z2 is a closed set, defined by the following ideal
Z2=Im2#0#0
--We compare Z2 and X2
Sy=ring Z2
subyx=apply(6,i->(y_i=>x_(P4#i)))
ZZ2=sub(Z2,subyx)
ZZ2==X2
--They are not equal
--We can easily see that Z2 is the empty set, whereas X2 consists of one point e_{0,0,0,1}

--Ideal defining Y_3
y3={x_{0,0,0,0},x_{0,0,0,1},x_{0,1,1,1},x_{1,1,1,1}}
Y3=ideal(y3)
--Ideal defining V(f_{224}) \cap Y_1
X3=radical (Y3+KER4)
--Ideal defining T^{-1}(Y_1)
YY3=radical ideal(apply(y3,el -> sub(el,apply(P4, j->(x_j => Hhom#j)))))
--We compute the image Z3 = T(T^{-1}(Y_3))
Im3=totalImage(L4hom,YY3,Verbose => true)
--We find that Z3 is a closed set, defined by the following ideal
Z3=Im3#0#0
--We compare Z3 and X3
Sy=ring Z3
subyx=apply(6,i->(y_i=>x_(P4#i)))
ZZ3=sub(Z3,subyx)
ZZ3==X3
--They are not equal
primaryDecomposition X3
--We see that X3 cuts out 3 points e_{0,1,0,1}, e_{0,0,1,1}+sqrt(2)e_{0,1,0,1}, e_{0,0,1,1}-sqrt(2)e_{0,1,0,1}
--Whereas Z3 cuts out just 1 point e_{0,1,0,1}

--Ideal defining Y_4
y4={x_{0,0,0,0},x_{1,1,1,1},2*x_{0,0,0,1}+2*x_{0,0,1,1}+2*x_{0,1,1,1}+x_{0,1,0,1}}
Y4=ideal(y4)
--Ideal defining V(f_{224}) \cap Y_4
X4=radical (Y4+KER4)
--Ideal defining T^{-1}(Y_4)
YY4=ideal(apply(y4,el -> sub(el,apply(P4, j->(x_j => Hhom#j)))))
--We compute the image Z4 = T(T^{-1}(Y_4))
Im4=totalImage(L4hom,YY4,Verbose => true)
--We find that Z4 is a closed set, defined by the following ideal
Z4=Im4#0#0
--We compare Z4 and X4
Sy=ring Z4
subyx=apply(6,i->(y_i=>x_(P4#i)))
sub(Z4,subyx)==X4
--They are equal

--We can conclude that uMPS(2,2,4) is V(f224) minus the orbits of e_{0,0,0,1}, e_{0,0,1,1}+sqrt(2)e_{0,1,0,1}, e_{0,0,1,1}-sqrt(2)e_{0,1,0,1}
--To obtain a description as a constructible subset, we just need to compute these orbits are constructible subsets

restart
K=QQ
R=K[q,a,b,c,d]
--We will later put q=sqrt(2)
P4={{0,0,0,0},{0,0,0,1},{0,0,1,1},{0,1,1,1},{1,1,1,1},{0,1,0,1}}
M=genericMatrix(R,a,2,2)
M4=M**M**M**M
--The coefficient of (e_I)\ot(e_J)\ot(e_K)\ot(e_L) in the expansion of (Me_i)\ot(Me_j)\ot(Me_k)\ot(Me_l) can be found in the matrix M4, at position (8i+4j+2k+l,8I+4J+2K+L)
--We now construct a matrix MM representing the action of M on Cyc^4(\CC^2), in the usual basis given by the list P4.
MM=mutableMatrix(apply(P4,e->apply(P4,f->(M4_(8*e#0+4*e#1+2*e#2+e#3,8*f#0+4*f#1+2*f#2+f#3)+M4_(8*e#0+4*e#1+2*e#2+e#3,8*f#1+4*f#2+2*f#3+f#0)+M4_(8*e#0+4*e#1+2*e#2+e#3,8*f#2+4*f#3+2*f#0+f#1)+M4_(8*e#0+4*e#1+2*e#2+e#3,8*f#3+4*f#0+2*f#1+f#2)))));
columnMult(MM,0,1/4);
columnMult(MM,4,1/4);
MM=matrix(columnMult(MM,5,1/2))

--Our first point is given by 
p1=vector({0,1,0,0,0,0})
--So a general point in the orbit of p1 is
pp1=MM*p1
--We compute the set of all tensors of the form G.p1, where G might be singular
L1=(flatten entries pp1)
loadPackage "TotalImage"
TI1=totalImage(L1,Verbose=>true)
--We see that this set is closed, and we can obtain its defining ideal
J1=TI1#0#0
S=ring J1
S1=K[apply(P4,j->x_j),MonomialOrder=>Lex]
I1=sub(J1,apply(6,i->(y_(i)=>x_(P4#i))))
gens gb I1
--Hence the only tensors that might be in the boundary of the orbit of p1 are the ones of the form G.p1, where G is singular
--But if G is a singular matrix, it has rank 1, and then G.p1 will be a rank one tensor!
--Since p1 has rank greater than 1, we conclude that its orbit is V(I1)\V(I), where I is the ideal defining the variety of rank 1 cyclically symmetric tensors. 

--The other 2 points are given by 
p2=vector({0,0,1,0,0,q})
--Where q^2=2.
--So a general point in the orbit of p2 is
pp2=MM*p2
--We compute the set of all tensors of the form G(e_{0,0,1,1}+qe_{0,1,0,1}), where G might be singular, for any q
L2=(flatten entries pp2)|{q}
--The following computation takes several minutes
TI2=totalImage(L2,Verbose=>true)
--Putting q^2=2 we see that this set is closed, and we can obtain its defining ideal
J2=TI2#0#0
S=ring J2
S2=K[apply(P4,j->x_j),qq,MonomialOrder=>Lex]/(qq^2-2)
I2=sub(J2,apply(6,i->(y_(i+1)=>x_(P4#i)))|{y_7=>qq})
gens gb I2
--As before, the only tensors that might be in the boundary of the orbit of p2 have rank 1
--So conclude that its orbit is V(I2)\V(I), where I is the ideal defining the variety of rank 1 cyclically symmetric tensors. 