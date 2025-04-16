AttachSpec("spec");
Attach("torsion3.m");
Attach("transformations.m");

function Chabauty0Genus3(H)
/* 
    This function returns the rational points on a genus 3 hyperelliptic curve 
    of the form H : y^2 = f(x), where f is a polynomial of degree 7 or 8 with integer coefficients.
    It is assumed that the Jacobian J of the curve H has Mordell–Weil rank zero.
*/

   J := Jacobian(H);           // Retrieve the Jacobian J of the curve H
   g := Genus(H);              // The genus of the curve (should be 3 in this context)

   if Degree(H) eq 7 then      // Case where f has degree 7 (rational Weierstrass point at infinity)
      G, m := myTorsionSubgroup(J);           // Torsion subgroup of J, with an isomorphism m
      K := KummerVarietyG3(H);                // Kummer variety associated to curve H
      TK := { K | K ! ToKummerVariety(m(D)) : D in G | D ne G!0 };  // Images of torsion elements (except 0) on the Kummer variety

      f := HyperellipticPolynomials(H);       // Retrieve the polynomial f(x)
      points := {@ H | H![r[1], 0] : r in Roots(f) @};   // Add affine Weierstrass points (y = 0)
      points join:= PointsAtInfinity(H);                 // Add points at infinity (one or two depending on the model)

      // For each torsion point mapped via the Kummer, we check a Chabauty condition
      for t in TK do
         if t[g]^2 eq 4 * t[g-1] * t[g+1] and t[g-1] ne 0 then
            points join:= Points(H, -t[g]/(2*t[g-1]));  // Recover the corresponding rational points
         end if;
      end for;

   else 
   // Case where f has degree 8: we need to transform the model to use a rational Weierstrass point

      f := HyperellipticPolynomials(H);   // Retrieve f(x)
      alpha := Roots(f)[1][1];            // Take a rational root of f

      // Change of variable x ↦ (1 + αx)/x to obtain a model with a Weierstrass point at infinity
      F := Numerator(Evaluate(f, (1 + alpha*x)/x));  
      C := HyperellipticCurve(F);                             // New transformed curve
      H1 := SimplifiedModel(MinimalWeierstrassModel(C));      // Simplified and minimal model
      F1 := HyperellipticPolynomials(H1);                     // Polynomial of the transformed curve

      J1 := Jacobian(H1);                // Jacobian of the transformed curve
      G, m := myTorsionSubgroup(J1);     // Torsion subgroup of the Jacobian
      K := KummerVarietyG3(H1);          // Kummer variety associated to H1
      TK := { K | K ! ToKummerVariety(m(D)) : D in G | D ne G!0 };  // Images on the Kummer

      points_H1 := {@ H1 | H1![r1[1], 0] : r1 in Roots(F1) @}; // Weierstrass points of H1 (y = 0)
      points := {@ H | H![alpha, 0] @};                        // Corresponding point on H from transformation
      points_H1 join:= PointsAtInfinity(H1);                  // Points at infinity of H1
      points join:= PointsAtInfinity(H);                      // Points at infinity of H

      // Search for additional rational points via the Chabauty condition
      for t in TK do
         if t[g]^2 eq 4 * t[g-1] * t[g+1] and t[g-1] ne 0 then
            points_H1 join:= Points(H1, -t[g]/(2*t[g-1]));
         end if;
      end for;

      // Map points on H1 back to points on H using the inverse of the variable change
      for i in [1..#points_H1] do
         if points_H1[i][1] ne 0 then
            x := points_H1[i][1];
            points join:= Points(H, (1 + alpha * x)/x);
         else 
            points join:= Points(H, 0);  // Case x = 0 in the change of variable
         end if;
      end for;
   end if;

   return points;  // Return the set of rational points found on H
end function;
//Verify if the points returned by **Chabauty0Genus3** are the same as the known rational points in Magma with a height less than  10^5 .
function compare(H,  L)
    // height := 10^4;
    // L := Chabauty0Genus3(J);
    point_coords := L; ;
    candidat := RationalPoints(H: Bound:=10^4);
    if #point_coords eq  #candidat  then 
        return [], [];
    else 
        return #point_coords, #candidat;
    end if;
 end function;
 
 
function strategy_quotient(f)

/*Returns the rational points on the curve C of genus  3 of which J is isogenous to ExJ_H, where H is an hyperelliptic curve of genus 2, under the condition that J_H has Mordell-Weil rank <=1 and E Mordell-Weil rank >=1*/
P2<x, y, z> := ProjectiveSpace(Rationals(),2);
C := Curve(P2,Numerator(Evaluate(f,P2.1/P2.3)*P2.3^8-P2.3^6*P2.2^2));
phi1 := iso<C -> C | [-x,y,z],[-x,y,z]>; 
phi2 := iso<C -> C | [-x,-y,z],[-x,-y,z]>;
G1 := AutomorphismGroup(C,[phi1]);
G2 := AutomorphismGroup(C,[phi2]); 
E, m1 := CurveQuotient(G1);
H, m2 := CurveQuotient(G2);
J:=Jacobian(H);
if RankBound(Jacobian(E)) ne 0 then
    if RankBound(J) eq 0 then  
        RationalPoints_on_H:=Chabauty0(Jacobian(H));
        for i in [1..#RationalPoints_on_H] do
            RationalPoints_on_C:=RationalPoints(Difference(Pullback(m2, RationalPoints_on_H[i]), BaseScheme(m2)));
            return RationalPoints_on_C;
        end for; 
    elif  RankBound(J) eq 1 then
          ptsH:=RationalPoints(H: Bound:=1000);
          for i in [2..#ptsH] do
              PJ:=J! [ptsH[i], ptsH[1]];
              if Order(PJ) eq 0 then 
                 all_ptsH:=Chabauty(PJ: ptC:=ptsH[1]);
                 for P in all_ptsH do
                     preimageofp:= P @@ m2;
                     RationalPoints_on_C:=Points(preimageofp);
                     return RationalPoints_on_C;
                    end for;
                end if;
            end for;
    end if;
end if;

end function; 

