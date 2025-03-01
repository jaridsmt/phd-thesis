/*
This code includes functions that, given a 4 transposition group, construct
a potential axial algebra. The algebra needs to be checked postfactum to see if it is axial.
*/


// Function that returns the value of the Frobenius form between two axes a and b. It only returns values if the order of tau_atau_b is leq 4,because otherwise the value is not well-defined.
// a,b: transpositions of a 4-transposition group
// returns: a rational number.
function phi(a,b)
  if Order(a*b) eq 1 then
    return 1;
  elif Order(a*b) eq 2 then
    return 0;
  elif Order(a*b) eq 3 then
    return 1/4;
  elif Order(a*b) eq 4 then
    return 1/2;
  else
    return 0;
  end if;
end function;

// Function that, given a 4 tranposition group (G,Ax) constructs the Gram matrix of the (potential) Frobenius form
// of a Jordan type half axial algebra with this Miyamoto group, over a field of definition.
// G: group (can be either GrpPC or PermutationGroup)
// Ax: IndexedSet of 4-transpositions
// def_field: a field.
// returns: a matrix over def_field.
function GramMatrix(G,Ax,def_field)
n:= #Ax;
return Matrix(def_field,n,n,[[phi(Ax[i],Ax[j]) : i in [1..n]] : j in [1..n]]);
end function;


// Function that, given a 4 transposition group (G,Ax) tries to construct a Jordan type half axial algebra with G as Miyamoto group, and Ax as Miyamoto involutions.
// G: group (can be either GrpPC or PermutationGroup)
// Ax: IndexedSet of 4-transpositions
// def_field: field the algebra is constructed over. This doesn't actually have to be a field.
// returns: so: boolean, A: Algebra over def_field, groupelts: IndexedSet.
//          The first argument returns true if the algebra can exist, and false otherwise
//          The second argument returns the candidate algebra if the first argument is true
//          The third argument returns an IndexedSet of elements of Ax, where the axis A.i should precisely have Miyamoto involution groupelts[i]
function ConstructJordanType(G,Ax,def_field)
  n:= #Ax;
  W := RSpace(def_field, n,GramMatrix(G,Ax,def_field));
  relations := [];
  for i in [1..n] do
    for j in [1..n] do
      if Order(Ax[i]*Ax[j]) eq 4 then
        Append(~relations, W.i + W.(Index(Ax,Ax[i]^Ax[j])) -W.j - W.(Index(Ax,Ax[j]^Ax[i]))  );
      end if;
    end for;
  end for;
  N,proj := quo<W|relations>;
  m := Rank(N);
  //print "expected dimension " cat Sprint(m);

  try
    //check orthogonality of relations with axes
    for i in [1..n] do
      for j in [1..#relations] do
        assert InnerProduct(W.i,relations[j]) eq 0;
      end for;
    end for;
  catch e
    return false,_,_;
  end try;
  //select basis of idempotents
   basis:=[];
   index:=[];
   groupelts:=[];
   i:=1;
   while i le n and #basis lt m do
     if proj(W.i) notin sub<N|basis> then
       Append(~index,i);
       Append(~basis,proj(W.i));
       Append(~groupelts,Ax[i]);
     end if;
     i+:=1;
   end while;
   K:=KSpaceWithBasis(basis);
   products :=[[Coordinates(K,phi(Ax[index[i]],Ax[index[j]])*proj(W.index[i]) + 1/4*proj(W.index[j])-1/4*proj(W.(Index(Ax, Ax[index[j]]^Ax[index[i]]) ))) : i in [1..m]] : j in [1..m]];
   A := Algebra<def_field,m|products>;
  return true,A,groupelts;
end function;

//Function that constructs the Matsuo algebra for the Hall group, by using the construction in [Example 2.10, DMRS23]
//def_field: the field over which we construct the algebra
//returns: The Hall algebra over def_field. The axes are given by the canonical basis.
function ConstructHallMatsuoAlgebra(def_field)
  V := VectorSpace(FiniteField(3),4);
  basis := [a:a in V];
  H :=  RSpace(def_field,#basis);

  products := [[Eltseq(1/4*(H.i+H.j - H.(Index(basis,Star(V,basis[i],basis[j]))))) : i in [1..#basis]] : j in [1..#basis]];
  for i in [1..#basis] do
    products[i,i] := Eltseq(H.i);
  end for;
  A := Algebra<def_field,#basis|products>;
  return A;
end function;

//WARNING: This is a function supporting ConstructHallMatsuoAlgebra, do not use.
function Bullet(V,a,b)
  a_new := Eltseq(a);
  b_new := Eltseq(b);
  return V ! [a_new[1]+b_new[1],a_new[2]+b_new[2],a_new[3]+b_new[3],a_new[4]+b_new[4]+(a_new[1]*b_new[2]-a_new[2]*b_new[1])*(a_new[3]-b_new[3])];
end function;

//WARNING: This is a function supporting ConstructHallMatsuoAlgebra, do not use.
function Star(V,a,b)
  return Bullet(V,Bullet(V,a,b),Bullet(V,a,b));
end function;


/*
Some additional functions needed for the main script
*/

//Function that randomly checks if an algebra might be Jordan, by computing the Jordan identity 10 times.
//A: algebra over a field.
//returns: true is A is likely to be Jordan, and false otherwise.
function IsLikelyJordan(A)
  output := true;
  n := Dimension(A);
  for i in [1..10] do
    v:= [Random(1,100) : i in [1..n]];
    x := A ! v;
    w:= [Random(1,100) : i in [1..n]];
    y := A ! w;
    output and:= (x*y)*(x*x) eq x*(y*(x*x)) ;
  end for;
  return output;
end function;


//Function that checks if a polycyclic group is an N transposition group. Will return false if the group has too many (>20?) conjugacy classes of involutions.
//G: polycyclic group (stored as PCGroup)
//N: positive integer.
//returns: so: boolean, G: PCGroup, transpositons: IndexedSetToSet
// so is true when (G,transpositions) is an N-transposition group.
//WARNING: function will return false if G contains too many conjugacy classes of involutions.
function IsNTranspositionGroupPC(G,N)
  n:= Order(G);
  conjclasses:= ConjugacyClasses(G);
  endindex := 1;
  while endindex lt #conjclasses and conjclasses[endindex+1][1] eq 2 do
    endindex +:=1;
  end while;
  totalindexset := {2..endindex};
  try
    powerset := Subsets(totalindexset);
    for indexset in powerset do
      transpositions := {};
      for j in indexset do
        transpositions join:= Class(G,conjclasses[j][3]);
      end for;
      if Order(sub< G| transpositions>) eq n then
        order4 := true;
        for trans1 in transpositions do
          for trans2 in transpositions do
            if not order4 then
              continue indexset;
            end if;
            order4 := Order(trans1*trans2) le N;
          end for;
        end for;
        if order4 then
          return true,G,SetToIndexedSet(transpositions);
        end if;
      end if;
    end for;
    return false,_,_;
  catch e
      return false,_,_;
    end try;
end function;
