AttachSpec("spec");
import "heights.m": normalize;
import "transformations.m": KummerTransformation;
import "torsion3.m": normalizetoaffine;


function PointOnKummer(C, P, p, b, B)
// C = genus 3 curve over the rationals,
// P = point on Jacobian over F_p,
// b = bound for p-adic approximation precision. (Section 4.4)
// B = height bound for torsion points (Theorem 3.15)
Cp:=ChangeRing(C, GF(p));
n:=Order(P);
prec:=1;
if n eq 2 then 
 print "Two torsion point";
 end if;
if n gt 1 and  n mod 2 eq 0 then
        m := 1 - n; // smallest m congruent to 1 mod n
        doubleflag := false;
 else
    a := EulerPhi(n);
        for d in Divisors(a) do
            if 2^d mod n eq 1 then
                order := d;
                break;
            end if;
        end for;
        m := 2^order;
        if (m - 1) mod p eq 0 then
            doubleflag := false;
            m := 1 - n;
        else
            doubleflag := true;
        end if;
       
 end if;
K := KummerVarietyG3(C);
// first lift
    F := GF(p);
    Kp := KummerVarietyG3(Cp);
    PK:= Eltseq(ToKummerVariety(P));
    // applies LLL-reduction to find a short vector. 
    L := Lattice(8, ChangeUniverse(Eltseq(PK), Integers())
                   cat [p,0,0,0,0,0,0,0, 0,p,0,0,0,0,0,0, 0,0,p,0,0,0,0,0, 0,0,0,p,0,0,0,0,
                        0,0,0,0,p,0,0,0, 0,0,0,0,0,p,0,0, 0,0,0,0,0,0,p,0, 0,0,0,0,0,0,0,p]);
    app := Eltseq(Basis(L)[1]);
       while prec lt b do // This iterates Step 4.
        // next lift
        newprec := Min(2*prec,b);
        oldF := F;
        F := Integers(p^newprec);
        // Onew := O(F!p^newprec);
        OldKp := Kp;
        Kp := KummerVarietyG3(C: Ambient := ProjectiveSpace(F, 7));
        // lift point to P^7 with new precision
        s := ChangeUniverse(Eltseq(PK), Integers()); 
        // uses a step in multivariate Newton Iteration to ensure that s
        // lifts to a point on the Kummer with sufficient precision.
        P_int := ChangeUniverse(Eltseq(s), Integers());
        kv := -Vector(oldF, [oldF| ExactQuotient(Evaluate(eqn, P_int), p^prec) : eqn in Equations(K)]); 
        jac := JacobianMatrix(DefiningEquations(OldKp));
        dkv := Matrix(oldF, [[Evaluate(jac[i,j], Eltseq(PK)) : j in [1..NumberOfColumns(jac)]]
                          : i in [1..NumberOfRows(jac)]]);
        if Rank(dkv) lt 4 then
            print "Working on point:", s;
            error "Singularity detected!";
        end if;
        sol, ker := Solution(Transpose(dkv), kv);
        sol := ChangeRing(sol, Integers());
        s1 := s;
        s1 := Vector(s) + p^prec * sol; // this is the actual Newton iteration step.
        if not doubleflag then	
            s2 := Kp!Eltseq(Multiple(C, m, Kp!Eltseq(s1) : Ambient := ProjectiveSpace(F, 7)));
        else
            s2 := s1;
            for i := 1 to order do
                s2 := Double(C, Kp!Eltseq(s2) : Ambient := ProjectiveSpace(F, 7));
            end for;
        end if;
        s1 := ChangeRing(s1, F);	
        s1 := normalizetoaffine(Eltseq(s1));		
        s2 := normalizetoaffine(Eltseq(s2));
        i := 1;
        while i ne 9 and Integers() ! (s1[i] - s2[i]) mod p^prec eq 0 do i +:= 1; end while;
        if i ne 9 then print p, prec, s1, s2; end if;
        error if i ne 9,
	        "LiftTorsionPoint: Precision loss!!";
        PK := [F | (m*(Integers()!s1[i]) - Integers()!s2[i])/(m-1) : i in [1..8] ];  
        // compute approximation
        q := p^newprec;
        // we already check whether we have found a lift with each iteration (Remark 4.17)
        L := Lattice(8, ChangeUniverse(PK, Integers())
                       cat [q,0,0,0,0,0,0,0, 0,q,0,0,0,0,0,0, 0,0,q,0,0,0,0,0, 0,0,0,q,0,0,0,0,
                            0,0,0,0,q,0,0,0, 0,0,0,0,0,q,0,0, 0,0,0,0,0,0,q,0, 0,0,0,0,0,0,0,q]);
        app1 := Eltseq(Basis(L)[1]);
        if app eq app1 and IsPointOnKummer(C, app1) then
            ht := Max([Height(c) : c in Eltseq(app)]);
            if ht gt B then 
                // Height too large for a torsion point.
                "too large";
                return false, _; 
            end if;
            PQ := K!app1;
            if Multiple(C, n, PQ) eq KummerOrigin(C) then
                if  doesLiftToJacobian(C, PQ)  then
                        return app1;
                  end if;
            end if; 
        end if;
          prec := newprec; app := app1; // prepare for new iteration.
    end while;
    ht := Max([Height(c) : c in Eltseq(app)]);
    if ht gt B then 
        // Height too large for a torsion point.
        return false, _; 
    end if;
    if not IsPointOnKummer(C, app) then 
        //"Point not on Kummer";
        return false, _; 
    end if;
	PQ := K!app;
    if Multiple(C, n, PQ) ne KummerOrigin(C) then 
        //"not torsion";
        return false, _; 
    end if;
    if  doesLiftToJacobian(C, PQ)  then
       return app;
     end if;
 end function; 
 function ComputeValidPoints(C, G, p, b, B)
    valid_results := [];
    for P in G do
        try
            result := PointOnKummer(C, P, p, b, B);
            if result cmpeq false then
                continue;
            elif Type(result) eq SeqEnum then  // Vérifie si le retour est bien une séquence (app ou app1)
                Append(~valid_results, result);
            end if;
        catch e
            if "Singularity detected!" in e`Object then
                print "Singularity detected at point:", P, "- Skipping...";
                continue;
            //else error e;  // Lève l'erreur si ce n'est pas une singularité  continue;
            end if;
        end try;
    end for;
    return valid_results;
end function;
  
 function Chabauty0Genus3(C, V)
   // V:= ComputeValidPoints(C, G, p, b, B);
   // C is hyperelliptic curve given by a model  of  degree 8
    g:=Genus(C);
    K:= KummerVarietyG3(C);
    points := PointsAtInfinity(C);// if the leading coeficient is square in Q
    TK := { K | K ! ToKummerVariety(D) : D in L }; 
    TK :={K| K!app: app in V};
    for t in TK do
      if t[3]^2 eq 4*t[2]*t[4] and t[2] ne 0 then
         points join:= Points(C, -t[3]/2/t[2]);
      end if;
   end for;
   return points;
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
 
