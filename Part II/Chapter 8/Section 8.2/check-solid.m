/*
This file contains function to check if the line spanned by two axes in an axial algebra is solid. Currently only implemented if their order is 3 or 4.

*/

R<x>:=PolynomialRing(Rationals());
field<x,y> := NumberField([x^2+1,x^2+x+1]);
invariate_field<t> := FunctionField(field);
load "fusionlaw.magma";



function CheckSolidLine3(alg,a,b)
  sigma := a*b-1/2*a-1/2*b;
  id_B := -8/3*sigma;
  assert id_B*a eq a and id_B*id_B eq id_B and id_B*b eq b;
  sum := a-1/2*id_B;
  difference := b-1/2*id_B;
  f := (y*sum-difference)/(2*y+1);
  e := -(y^2*sum -difference)/(2*y+1);
  assert f^2 eq Zero(alg) and e^2 eq Zero(alg);
  testidempotent := t*e+1/2*id_B+t^(-1)*f;
  //print "is e-a idempotent? " cat Sprint(CheckJordanfusionlaw(alg,-e+1/2*id_B-f));
  //eigv, fustab  := fusion_law(alg,-e+1/2*id_B-f);
	//PrintFile("FusionLawe_a.txt", eigv);
	//PrintFile("FusionLawe_a.txt", fustab);
  //PrintFile("FusionLawe_a.txt", "####################################################");
  return CheckJordanfusionlaw(alg,testidempotent);
end function;

// This is a small check to see if my code is correct, i.e. that the newly constructed idempotents are in fact axes in the 2-generated subalgebra.
productaa := [1,0,0];
productab := [1/2,1/2,1];
productbb := [0,1,0];
productasigma := [-3/8,0,0];
productbsigma := [0,-3/8,0];
productsigmasigma := [0,0,-3/8];
products := [[productaa,productab,productasigma],[productab,productbb,productbsigma],[productasigma,productbsigma,productsigmasigma] ];
B := Algebra<invariate_field,3|products>;
a := B.1;
b := B.2;
sigma := B.3;
id_B := -8/3*sigma;
assert id_B*a eq a and id_B*id_B eq id_B and id_B*b eq b;
sum := a-1/2*id_B;
difference := b-1/2*id_B;
f := (y*sum-difference)/(2*y+1);
e := -(y^2*sum -difference)/(2*y+1);
assert f^2 eq Zero(B) and e^2 eq Zero(B);
testidempotent := t*e+1/2*id_B+t^(-1)*f;
assert CheckJordanfusionlaw(B,a) and CheckJordanfusionlaw(B,b);
assert CheckJordanfusionlaw(B,testidempotent);
//END OF CHECK

function CheckSolidLine4(alg,a,b)
  sigma := a*b-1/2*a-1/2*b;
  id_B := -4*sigma;
  sum := a-1/2*id_B;
  difference := b-1/2*id_B;
  e := -x*(x*sum+difference)/(2);
  f := (sum +x*difference)/2;
  testidempotent := t*e+1/2*id_B+t^(-1)*f;
  return CheckJordanfusionlaw(alg,testidempotent);
end function;

// This is a small check to see if my code is correct, i.e. that the newly constructed idempotents are in fact axes in the 2-generated subalgebra.
productaa := [1,0,0];
productab := [1/2,1/2,1];
productbb := [0,1,0];
productasigma := [-1/4,0,0];
productbsigma := [0,-1/4,0];
productsigmasigma := [0,0,-1/4];
products := [[productaa,productab,productasigma],[productab,productbb,productbsigma],[productasigma,productbsigma,productsigmasigma] ];
B := Algebra<invariate_field,3|products>;
assert CheckJordanfusionlaw(B,B.2) and CheckJordanfusionlaw(B,B.1);
id_B_1 := B ! [0,0,-4];
a_1 := B ![1,0,0];
b_1 := B ! [0,1,0];
sum_1 := a_1-1/2*id_B_1;
difference_1 := b_1-1/2*id_B_1;
e_1 := -x*(x*sum_1+difference_1)/(2);
f_1 := (sum_1 +x*difference_1)/2;
assert e_1^2 eq B ! [0,0,0] and f_1^2 eq B ! [0,0,0];
assert CheckJordanfusionlaw(B,t*e_1+1/2*id_B_1+t^(-1)*f_1);
//END OF CHECK


function CheckSolidLine(alg,a,b,n)
  alg_new := Algebra<invariate_field,Dimension(alg)|[ [Eltseq(BasisProducts(alg)[i,j]): i in [1..Dimension(alg)] ] : j in [1..Dimension(alg)]]>;
  a_new := alg_new ! Eltseq(a);
  b_new := alg_new ! Eltseq(b);
  if n eq 3 then
    return CheckSolidLine3(alg_new,a_new,b_new);
  elif n eq 4 then
    return CheckSolidLine4(alg_new,a_new,b_new);
  else
    return true;
  end if;
end function;
