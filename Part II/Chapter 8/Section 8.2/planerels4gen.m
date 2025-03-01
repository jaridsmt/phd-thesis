load "4trans_axial_algebra.m";

/*
This is a standard function to print a nice formatted time elapsed.
*/
function print_time(t);
	if t le 60 then
		return Sprintf("%o seconds", t);
	end if;

	if t le 60*60 then
		return Sprintf("%o minutes", t/60.0);
	end if;

	if t le 3600*24 then
		return Sprintf("%o hours", t/3600.0);
	end if;

	if t le 3600*24*365 then
		return Sprintf("%o days", t/(3600*24));
	end if;

	return Sprintf("%o years", t/(3600*24*365));
end function;

/*
Given a 3-transposition group (W,transpo), compute the expected dimension of the Lie algebra of derivations of the Matsuo algebra over the field "field".
It returns the dimension of the Lie algebra (when only considering "local" equations) dim, and the matrix of "local" equations M.
*/
function DimensionOfLieAlgebra(W,transpo,field)
  starttime := Realtime();
	//This function constructs the Matsuo algebra.
  so,A,groupelts := ConstructJordanType(W,transpo,field);
  n := Dimension(A);
	//We will create an arbitrary linear map (d_{n*(i-1)+j})_{i,j}, and write down the equations for this to be a derivation of the Matsuo algebra.
  field_of_det := PolynomialRing(field, n^2);
  A := ChangeRing(A,field_of_det);
  der := Matrix(field_of_det,n,n,[field_of_det.i : i in [1..n^2] ]);
	//We will use SparseMatrix in the hope that this will make things more efficient.
  M := SparseMatrix(field);
  for i in [1..n] do
		//Do A.i*der(A.i) manually to have nicer equations.
		row := NumberOfRows(M)+1;
		helper :=  der[i,i] ;
		//This is not efficient, but it does not really have to be.
		for column  in [1..n^2] do
			test := Coefficient(helper,column,1);
			if  not test eq 0 then
				SetEntry(~M,row,column,test);
			end if;
		end for;

    for j in [i..n] do
      //Check whether der is a derivation. Each coefficient (with respect to the canonical basis)
			//Gives an equation that the d_i should satisfy.
      helper :=Eltseq( (A.i*A.j)*der - (A.i*der)*A.j -(A.j*der)*A.i );
      for k in [1..#helper] do
				//Ignore non-local equations.
				if ((not k eq i) and (not k eq j)) then
	        row := NumberOfRows(M)+1;
					//For each d_i, record the coefficient of d_i into the matrix of equations.
	        for column  in [1..n^2] do
	          test := Coefficient(helper[k],column,1);
	          if  not test eq 0 then
	            SetEntry(~M,row,column,test);
	          end if;
	        end for;
				end if;
      end for;
    end for;
  end for;
	//Now, the rows of M are precisely equations of the d_i that are both necessary and sufficient
	//for the linear map der to be a derivation.
  Sprintf( "%o elapsed",print_time(Realtime() - starttime));
  Sprint("Found all equations");
	//Compute the dimension of the kernel of M, as this is precisely equal to the dimension of the Lie algebra.
  dim := n^2 -Rank(M);
  Sprintf( "%o elapsed",print_time(Realtime() - starttime));
  return dim,M;
end function;


/*
Function to create the extended Weyl group G  = k^n : W(KC). Here "KC" should be a Cartan string,
and k equal to 2 or 3. It returns the group G, together with its conjugacy class of $3$-transpositions.
*/
function ExtendedWeylGroup(KC,k)
  R := RootDatum(KC);
  W:= WeylGroup(GrpMat,GroupOfLieType(R,11));
  n := Rank(W);
  G:=MatrixGroup<n,GF(k) | [Matrix(GF(k),SimpleReflectionMatrices(W)[i]): i in [1..n]]>;
  M := GModule(G);
  K,psi := SplitExtension(CohomologyModule(G,M));
  //compute inverse image
  pre := (G.1)@@psi;
  ker := Kernel(psi);
  K2,gamma := PermutationGroup(K);
  inv := gamma(pre);
  ker2 := gamma(ker);
  assert inv^2 eq Id(K2);
  transpositions := Orbit(K2,inv);
  for i in [2..n] do
    transpositions join:=Orbit(K2,gamma((G.i)@@psi));
  end for;
  return [* K2,transpositions, ker2 *];
end function;

groups:= [  ];

//####################################################
//W(A_4):=S_5
W:= CoxeterGroup(GrpPermCox,"A4");
trans := Orbit(W,W.1);
Append(~groups,[* W,trans *]);

//####################################################
//W(D_4)
W:= CoxeterGroup(GrpPermCox,"D4");
trans := Orbit(W,W.1);
Append(~groups,[* W,trans *]);

//#####################################################
//W_3(A3)
Append(~groups,ExtendedWeylGroup("A3",3));

//####################################################
//Affine quotient hall
G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^3,(a^b*c)^3,(a^b*d)^3,(a^c*d)^3,(b^c*d)^3,(a^b*c^d)^3,(a^c*b^d)^3,(a^d*b^c)^3,a*(b*c*d)^2*a^(-1)*(b*c*d)^(-2)>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);
assert(#transpo eq 27);

//####################################################
//2^6:SU_3(2)'
G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^2,((b^a)*c)^3,((b^d)*c)^3,((a^b)*(c^d))^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);

//####################################################
//Hall
G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^3,(a^b*c)^3,(a^b*d)^3,(a^c*d)^3,(b^c*d)^3,(a^b*c^d)^3,(a^c*b^d)^3,(a^d*b^c)^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);


//Loop to compute Lie algebra of groups in list groups.
for group in groups do
	Sprint("The dimension of the Matsuo algebra is");
  Sprint(#group[2]);
  Sprint("The dimension of the Lie algebra over Q");
	dim,M := DimensionOfLieAlgebra(group[1],group[2],Rationals());
	Sprintf("The upper bound for the dimension of the Lie algebra is %o", dim);
	M:=Matrix(M);
	nonperp := [];
	//Gather all transpositions collinear to the first one (called x), but do not count lines twice.
	for i in [1..#group[2]] do
		if (not group[2][i]^group[2][1] eq group[2][i]) and (not Index(group[2],group[2][i]^group[2][1]) in nonperp) then
			Append(~nonperp,i);
		end if;
	end for;
	boolint := true;
	bool3 := true;
	//For each element e collinear to x, check whether d(x)_e = 0 is an integral linear combination of local equations.
	//As $G$ acts transitively on points, this is sufficient.
	starttime :=  Realtime();
	i:= 1;
	//for elt in nonperp do
	while i le #nonperp and bool3 do
		elt := nonperp[i];
		eqn := Vector(Rationals(),[0 : j in [1.. elt-1]] cat [1] cat [0: j in [1..(#group[2])^2-elt]]);
		hassol, V,K := IsConsistent(M,eqn);
		if hassol then
			for i in [1..Ncols(V)] do
				boolint and:=IsIntegral(V[i]);
				bool3 and:= IsIntegral(6^5*V[i]);
			end for;
		end if;
		i := i+1;
	end while;
	//end for;
	Sprintf( "%o elapsed",print_time(Realtime() - starttime));
	Sprint("Is integralcombo");
	Sprint(boolint);
	Sprint("Is integral localised at 3 combo");
	Sprint(bool3);
  Sprint("#######################");
end for;

//separate loop for non-vertical lines in 3^3:S_n.
Sprint("This is 3^3:S4");
group := ExtendedWeylGroup("A3",3);
Sprint("The dimension of the Matsuo algebra is");
Sprint(#group[2]);
Sprint("The dimension of the Lie algebra over Q");
dim,M := DimensionOfLieAlgebra(group[1],group[2],Rationals());
Sprintf("The upper bound for the dimension of the Lie algebra is %o", dim);
M:=Matrix(M);
nonperp := [];
//Gather all transpositions collinear to the first one (called x), but do not count lines twice, and ignore vertical lines.
for i in [1..#group[2]] do
	if (not group[2][i]^group[2][1] eq group[2][i]) and (not Index(group[2],group[2][i]^group[2][1]) in nonperp) and not group[2][i]^(-1)*group[2][1] in group[3] then
		Append(~nonperp,i);
	end if;
end for;
boolint := true;
bool3 := true;
//For each element e collinear to x, check whether d(x)_e = 0 is an integral linear combination of local equations.
//As $G$ acts transitively on points, this is sufficient.
for elt in nonperp do
	eqn := Vector(Rationals(),[0 : j in [1.. elt-1]] cat [1] cat [0: j in [1..(#group[2])^2-elt]]);
	hassol, V,K := IsConsistent(M,eqn);
	assert hassol;
	for i in [1..Ncols(V)] do
		boolint and:=IsIntegral(V[i]);
		bool3 and:= IsIntegral(9*V[i]);
	end for;
end for;
Sprint("Is integralcombo");
Sprint(boolint);
Sprint("Is integral localised at 3 combo");
Sprint(bool3);
Sprint("#######################");
