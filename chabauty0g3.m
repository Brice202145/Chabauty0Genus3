load"torsionsubgroup.m";


function Chabauty0Genus3(J)

/*Returns the rational points on the curve H :y^2:=f(x) where f in Z[x] of genus 3 of which J  is the Jacobian, under the condition that J has Mordell-Weil rank zero.*/
   H:= Curve(J);
   g:=Genus(H);
   G, m := myTorsionSubgroup(J);
   K := KummerVarietyG3(H);
   TK := { K | K ! ToKummerVariety(m(D)) : D in G | D ne G!0 };
   f := HyperellipticPolynomials(H);
   points := {@ H | H![r[1],0] : r in Roots(f) @};
   points join:= PointsAtInfinity(H);
      for t in TK do
      if t[g]^2 eq 4*t[g-1]*t[g+1] and t[g-1] ne 0 then
         points join:= Points(H, Abs(t[g])/2/t[g-1]);
      end if;
   end for;
   return points;
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
