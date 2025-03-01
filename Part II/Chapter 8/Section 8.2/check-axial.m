/*
This file contains functions used to check if elements of an algebra are jordan type half axes,
and functions to check if the canonical basis of an algebra are all jordan type half axes.
*/


function CheckEigenvalues(A,a)
  output := true;
  for i in [1..Dimension(A)] do
    b:= A.i ;
    output and:= (1/2*(a*b) +(a*(a*(a*b))) eq 3/2*(a*(a*b)));
  end for;
  return output;
end function;

function CheckZeroZero(A,a)
  output := true;
  for i in [1..Dimension(A)] do
    for j in [1..Dimension(A)] do
      b:= A.i;
      c:= A.j;
      b_new := a*(a*b) -3/2*(a*b) + 1/2*b;
      c_new := a*(a*c) -3/2*(a*c) + 1/2*c;
      output and:= ( a*(b_new*c_new) eq 0*(b_new*c_new) );
    end for;
  end for;
  return output;
end function;

function CheckHalfHalf(A,a)
  output := true;
  for i in [1..Dimension(A)] do
    for j in [1..Dimension(A)] do
      b:= A.i;
      c:= A.j;
      b_new := a*(a*b) -(a*b) ;
      c_new := a*(a*c) -(a*c);
      output and:= ( a*(a*(b_new*c_new)) eq a*(b_new*c_new) );
    end for;
  end for;
  return output;
end function;

function CheckZeroHalf(A,a)
  output := true;
  for i in [1..Dimension(A)] do
    for j in [1..Dimension(A)] do
      b:= A.i;
      c:= A.j;
      b_new := a*(a*b) -(a*b) ;
      c_new := a*(a*c) -3/2*(a*c) + 1/2*c;
      output and:= ( a*(b_new*c_new) eq 1/2*(b_new*c_new) );
    end for;
  end for;
  return output;
end function;

function CheckJordanfusionlaw(A,a)
  output := (a^2 eq a);
  output and:= CheckEigenvalues(A,a);
  output and:= CheckHalfHalf(A,a);
  output and:= CheckZeroHalf(A,a);
  output and:= CheckZeroZero(A,a);
  return output;
end function;

function IsAxial(A)
  n:= Dimension(A);
  output := true;
  for i in [1..n] do
    if output then
      output and:= CheckJordanfusionlaw(A,A.i);
    end if;
  end for;
  return output;
end function;
