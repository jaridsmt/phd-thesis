load "4trans_axial_algebra.m";
load "check-axial.m";
load "check-solid.m";

//computes dimension of derivations of  5-generated matsuo algebras for rationals and field of three elements


//time printing function
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


function DimensionOfLieAlgebra(W,transpo,field)
  starttime := Realtime();
  so,A,groupelts := ConstructJordanType(W,transpo,field);
  n := Dimension(A);
  field_of_det := PolynomialRing(field, n^2);
  A := ChangeRing(A,field_of_det);
  der := Matrix(field_of_det,n,n,[field_of_det.i : i in [1..n^2] ]);

  function phi(a,b)
    if a eq b then
      return 1;
    end if;
    if a*b eq Zero(A) then
      return 0;
    end if;
    return 1/4;
  end function;
  F := Matrix(field_of_det,n,n,[[phi(A.i,A.j) : i in [1..n]] : j in [1..n]]);

  M := SparseMatrix(field);
  for i in [1..n] do
		//Do A.i*der(A.i) manually to have nicer equations.
		/*
		row := NumberOfRows(M)+1;
		helper :=  der[i,i] ;
		for column  in [1..n^2] do
			test := Coefficient(helper,column,1);
			if  not test eq 0 then
				SetEntry(~M,row,column,test);
			end if;
		end for;
		*/
    for j in [i..n] do
      //multiplication checking.
      helper :=Eltseq( (A.i*A.j)*der - (A.i*der)*A.j -(A.j*der)*A.i );
      for k in [1..#helper] do
				//Ignore non-local equations. CURRENTLY TURNED OFF
				//if ((not k eq i) and (not k eq j)) then
	        row := NumberOfRows(M)+1;
	        for column  in [1..n^2] do
	          test := Coefficient(helper[k],column,1);
	          if  not test eq 0 then
	            SetEntry(~M,row,column,test);
	          end if;
	        end for;
				//end if;
      end for;
    end for;
  end for;

  Sprintf( "%o elapsed",print_time(Realtime() - starttime));
  Sprint("Found all equations");
  dim := n^2 -Rank(M);
  Sprintf( "%o elapsed",print_time(Realtime() - starttime));
  dim_rad := n-Rank(F);
  Sprintf( "Dimension of radical: %o",dim_rad);
  return dim,M;
end function;

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
  return [* K2,transpositions *];
end function;

groups:= [  ];


//#####################################################
W:= CoxeterGroup(GrpPermCox,"A3");
trans := Orbit(W,W.1);
Append(~groups,[* W,trans *]);

//####################################################
G := Group<a,b,c|a^2,b^2,c^2,(a*b)^3,(a*c)^3,(b*c)^3,(a^b*c)^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);

//####################################################
W:= CoxeterGroup(GrpPermCox,"D4");
trans := Orbit(W,W.1);
Append(~groups,[* W,trans *]);

//#####################################################
Append(~groups,ExtendedWeylGroup("A4",3));

//####################################################
G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^2,((b^a)*c)^3,((b^d)*c)^3,((a^b)*(c^d))^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);
/*
//####################################################
G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^3,(a^b*c)^3,(a^b*d)^3,(a^c*d)^3,(b^c*d)^3,(a^b*c^d)^3,(a^c*b^d)^3,(a^d*b^c)^3,a*(b*c*d)^2*a^(-1)*(b*c*d)^(-2)>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);

//####################################################
G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^3,(a^b*c)^3,(a^b*d)^3,(a^c*d)^3,(b^c*d)^3,(a^b*c^d)^3,(a^c*b^d)^3,(a^d*b^c)^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);



//#####################################################
//Append(~groups,ExtendedWeylGroup("D4",2));

//#####################################################
//Append(~groups,ExtendedWeylGroup("A4",2));

//#####################################################
//Append(~groups,ExtendedWeylGroup("D4",3));

//#####################################################
//Append(~groups,ExtendedWeylGroup("A4",3));

//####################################################
//F(5,45)
G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(b*c)^3,(c*d)^3,(d*e)^3,(b*d)^3,(a*c)^2,(a*d)^2,(a*e)^2,(b*e)^2,(c*e)^2,(b^c*d)^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);

//####################################################
//F(5,72)
G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(a*c)^2,(a*d)^2,(a*e)^2,(b*c)^3,(c*d)^3,(d*b)^3,(b*e)^3,(c*e)^2,(d*e)^2,(b^c*d)^3,(a^((b*c*d)^2)*e)^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Append(~groups,[* W,transpo *]);

//####################################################
//F(5,162)
//G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(a*c)^2,(a*d)^2,(a*e)^3,(b*c)^3,(b*d)^3,(b*e)^3,(c*d)^3,(c*e)^2,(d*e)^2,(b^a*e)^3,(b^c*d)^3,(b^(a*e)*b^(c*d))^3,(b^(a*e)*b^(d*c))^3>;
//W:=PermutationGroup(G);
//transpo := Orbit(W,W.1);
//Append(~groups,[* W,transpo *]);

//####################################################
//F(5,54)
G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(a*c)^2,(a*d)^2,(a*e)^3,(b*c)^3,(b*d)^3,(b*e)^3,(c*d)^3,(c*e)^2,(d*e)^2,((b^a)*e)^3,((b^c)*d)^3,((b^(a*e))*(b^(c*d)))^3,((b^(a*e))*(b^(d*c)))^3,b^(a*c*d*b)*(a*b*e)^(-2)*b^(a*c*d*b)*(a*b*e)^(2)>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
Sprint(#transpo);
Append(~groups,[* W,transpo *]);

//####################################################
//F(5,165)
//G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(a*c)^3,(a*d)^2,(a*e)^2,(b*c)^3,(b*d)^3,(b*e)^2,(c*d)^3,(c*e)^2,(d*e)^3,(b^a*c)^3,(b^d*c)^3,(a^b*c^d)^3>;
//W:=PermutationGroup(G);
//transpo := Orbit(W,W.1);
//Sprint(#transpo);
//Append(~groups,[* W,transpo *]);

//####################################################
//F(5,360)
//G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(a*c)^3,(a*d)^2,(a*e)^2,(b*c)^3,(b*d)^3,(b*e)^2,(c*d)^3,(c*e)^3,(d*e)^2,(b^a*c)^3,(b^d*c)^3,(a^b*c^d)^3,(d^((a*b*c)^2*e))^3>;
//W:=PermutationGroup(G);
//transpo := Orbit(W,W.1);
//Append(~groups,[* W,transpo *]);

//####################################################
//F(5,576)
//G := Group<a,b,c,d,e|a^2,b^2,c^2,d^2,e^2,(a*b)^3,(a*c)^3,(a*d)^2,(a*e)^2,(b*c)^3,(b*d)^3,(b*e)^2,(c*d)^3,(c*e)^3,(d*e)^2,(b^a*c)^3,(b^d*c)^3,(a^b*c^d)^3,(d^((a*b*c)^2*e))^3>;
//W:=PermutationGroup(G);
//transpo := Orbit(W,W.1);
//Append(~groups,[* W,transpo *]);
*/
/*
W:= CoxeterGroup(GrpPermCox,"A3");
trans := Orbit(W,W.1);
Append(~groups,[* W,trans *]);

W:= CoxeterGroup(GrpPermCox,"D4");
trans := Orbit(W,W.1);
Append(~groups,[* W,trans *]);

Append(~groups,ExtendedWeylGroup("A2",3));

Append(~groups,ExtendedWeylGroup("A5",2));


G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^3,(a^b*c)^3,(a^b*d)^3,(a^c*d)^3,(b^c*d)^3,(a^b*c^d)^3,(a^c*b^d)^3,(a^d*b^c)^3,a*(b*c*d)^2*a^(-1)*(b*c*d)^(-2)>;
W := PermutationGroup(G);
transpos := Orbit(W,W.1);
Append(~groups,[*W,transpos*]);


G := Group<a,b,c,d|a^2,b^2,c^2,d^2,(b*c)^3,(c*a)^3,(a*b)^3,(b*d)^3,(d*c)^3,(a*d)^3,(a^b*c)^3,(a^b*d)^3,(a^c*d)^3,(b^c*d)^3,(a^b*c^d)^3,(a^c*b^d)^3,(a^d*b^c)^3>;
W:=PermutationGroup(G);
transpo := Orbit(W,W.1);
assert #transpo eq 81;
Append(~groups,[* W,transpo *]);


G:= PrimitiveGroups(63)[5];
transpositions := Orbit(G,ConjugacyClasses(G)[2][3]);
assert #transpositions eq 63;
Append(~groups,[* G,transpositions *]);

G:= PrimitiveGroups(136)[9];
transpositions := Orbit(G,ConjugacyClasses(G)[2][3]);
assert #transpositions eq 136;
Append(~groups,[* G,transpositions *]);
*/






for group in groups do
  Sprint("The dimension of the Matsuo algebra is");
  Sprint(#group[2]);
  Sprint("The dimension of the Lie algebra over GF(3)");
  Sprint(DimensionOfLieAlgebra(group[1],group[2],GF(3)));
  Sprint("The dimension of the Lie algebra over Q");
	test := DimensionOfLieAlgebra(group[1],group[2],Rationals());
  Sprint(test);
  Sprint("#######################");
end for;
