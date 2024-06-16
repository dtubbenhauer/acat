//Test for idempotents and partial traces:
AttachSpec("ASLoc.spec");

//Start with Case B2 and d = 1, w = d21;
procedure B2_complete()
    //We run all tests step by step and return the total time and space needed:
    ResetMaximumMemoryUsage();
    T := Time();

    //Setup of category
    //AttachSpec("ASLoc.spec");
    cartanMat := CartanMatrix("B2");
    W := CoxeterGroup(GrpFPCox, cartanMat);
    B := BSCategory(CartanMatrix("B2"), W);
    FR := B`FR;
    FA := B`FAct;

    //Action of Group, needed for Tensorproduct later
    act := function(w)
	    return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;

    //Now we create idempotents
    //ei will be the idempotent of the word of length i
    e1 := BSId(B,1)`stdmor;
    e2 := Tensor(act, e1, [id,t]);

    //For e3 one need a sum of two terms; 
    //We use the shorthand fi_s for the tensor product of ei with s
    //We then define up and down maps from fi_s to e(i-1)
    //the coefficient k1_3 is then computed as in the paper
    f2_s := Tensor(act, e2, [id,s]);
    d2_1 := e1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * f2_s;
    u2_1 := f2_s * LocalisedLLUp(B,[1,2,1],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := b1_3`mat[1,1] / e1`mat[1,1];
    e3 := f2_s - 1/k1_3 * u2_1 * d2_1;

    assert e3 eq e3 * e3;
    
    //Now we check the positive root:
    //The positive root should be 3/2*FR.1 + 2*FR.2; Check:    
    root := 3/2*FR.1 + 2*FR.2;
    assert Matrix(Mult(B,1)`stdmor * Tensor(act, BSId(B,1)`stdmor, root*BSId(B,1)`stdmor) * Comult(B,1)`stdmor) eq Matrix(BSId(B,1)`stdmor);
    assert Matrix(Mult(B,2)`stdmor * Tensor(act, BSId(B,2)`stdmor, root*BSId(B,2)`stdmor) * Comult(B,2)`stdmor) eq Matrix(BSId(B,2)`stdmor);

    //Finally we compute the partial trace and dimension:
    //We create partial trace map around e3 to go to e1 
    dtop121 := LocalisedLLDown(B,[1,2,1,1,2],[1,1,1,1,1]);
    dbot121 := LocalisedLLUp(B,[1,2,1,1,2],[1,1,1,1,1]);
    partial_trace1 := dtop121 * (Tensor(act,e3,root*e2)) * dbot121; 

    //The dimension is then partial_1(partial_trace)
    trace_morphism := Mult(B,1)`stdmor * (Tensor(act, partial_trace1, e1)) * Comult(B,1)`stdmor;
    dim := Matrix(trace_morphism)[1,1] / Matrix(e1)[1,1];
    
    assert dim eq 1;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("All assertions correct. The dimension of ew is %o. Total time for the calculation took %o, used space was %o.", dim, T, S);
end procedure;

//Continue with Case G2 and d = 1, w = d2121;
procedure G2_complete()
    //We run all tests step by step and return the total time and space needed:
    ResetMaximumMemoryUsage();
    T := Time();

    //Setup of category
    //AttachSpec("ASLoc.spec");
    cartanMat := CartanMatrix("G2");
    W := CoxeterGroup(GrpFPCox, cartanMat);
    B := BSCategory(CartanMatrix("G2"), W);
    FR := B`FR;
    FA := B`FAct;

    //Action of Group, needed for Tensorproduct later
    act := function(w)
	    return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;

    //Now we create idempotents
    //ei will be the idempotent of the word of length i
    e1 := BSId(B,1)`stdmor;
    e2 := Tensor(act, e1, [id,t]);

    //For faster calculation we define quantum numbers 
    //two-color quantum numbers:
    q2 := -cartanMat[2,1];
    p2 := -cartanMat[1,2];
    q3 := q2*p2-1;
    p3 := q2*p2-1;
    q4 := q2*q3-q2;
    p4 := p2*p3-p2;

    //Build up next idempotents using down and up morphisms
    //di_j describes the morphism from ei to e(i-1); ui_j the other direction
    f2_s := Tensor(act, e2, [id,s]);
    d3_1 := LocalisedLLDown(B,[1,2,1],[1,0,0]);
    u3_1 := LocalisedLLUp(B,[1,2,1],[1,0,0]);
    e3 := f2_s + 1/q2 * f2_s * u3_1 * e1 * d3_1 * f2_s;

    f3_t :=  Tensor(act, e3, [id,t]);
    d4_2 := LocalisedLLDown(B,[1,2,1,2],[1,1,0,0]); 
    u4_2 := LocalisedLLUp(B,[1,2,1,2],[1,1,0,0]);
    g4_2 := q2/q3 * f3_t * u4_2 * e2 * d4_2 * f3_t;
    e4 := f3_t + g4_2;

    f4_s :=  Tensor(act, e4, [id,s]);
    u5_3 := LocalisedLLUp(B,[1,2,1,2,1],[1,1,1,0,0]);
    d5_3 := LocalisedLLDown(B,[1,2,1,2,1],[1,1,1,0,0]);
    g5_3 := q3/q4 * f4_s * u5_3 * e3 * d5_3 * f4_s;
    e5 := f4_s + g5_3;
    
    assert e3 eq e3 * e3;
    assert e4 eq e4 * e4;
    assert e5 eq e5 * e5;
    
    //Now we check the positive root:
    //The positive root should be 5*FR.1 + 3*FR.2; Check:    
    root := 5*FR.1 + 3*FR.2;
    assert Matrix(Mult(B,1)`stdmor * Tensor(act, BSId(B,1)`stdmor, root*BSId(B,1)`stdmor) * Comult(B,1)`stdmor) eq Matrix(BSId(B,1)`stdmor);
    assert Matrix(Mult(B,2)`stdmor * Tensor(act, BSId(B,2)`stdmor, root*BSId(B,2)`stdmor) * Comult(B,2)`stdmor) eq Matrix(BSId(B,2)`stdmor);

    //Finally we compute the partial trace and dimension:
    //We create partial trace map around e3 to go to e1 
    dtop5 := LocalisedLLDown(B,[1,2,1,2,1,1,2,1,2],[1,1,1,1,1,1,1,1,1]);
    dbot5 := LocalisedLLUp(B,[1,2,1,2,1,1,2,1,2],[1,1,1,1,1,1,1,1,1]);
    partial_trace1 := dtop5 * (Tensor(act,e5,root*BSId(B,[1,2,1,2])`stdmor)) * dbot5; 

    //The dimension is then partial_1(partial_trace)
    trace_morphism := Mult(B,1)`stdmor * (Tensor(act, partial_trace1, e1)) * Comult(B,1)`stdmor;
    dim := Matrix(trace_morphism)[1,1] / Matrix(e1)[1,1];
    
    assert dim eq 1;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("All assertions correct. The dimension of ew is %o. Total time for the calculation took %o, used space was %o.", dim, T, S);
end procedure;

//Now in case H3 the cell of $a$-value 3: d=232; w=d123
procedure H3_a3_complete()
    //We run all tests step by step and return the total time and space needed:
    ResetMaximumMemoryUsage();
    T := Time();

    AttachSpec("ASLoc.spec");
    carH3 := CartanMatrix("H3");
    W := CoxeterGroup(GrpFPCox, "H3");

    //The cartan matrix lives over a cyclotomic field including the golden ratio
    f := BaseRing(carH3);
    FR := RationalFunctionField(f,Rank(W));

    //We can construct the right BSCategory with the new field
    B := New(BSCat);
    B`C := carH3;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    FA := B`FAct;

    act := function(w)
	    return FActionByElt(B,w);
    end function;
    
    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;

    //Now we create idempotents
    //ei will be the idempotent of the word of length i
    e1 := BSId(B,2)`stdmor;
    e2 := Tensor(act, e1, [id,u]);

    //e3
    f2_t := Tensor(act, e2, [id,t]);
    d2_1 := e1 * LocalisedLLDown(B,[2,3,2],[1,0,0]) * f2_t;
    u2_1 := f2_t * LocalisedLLUp(B,[2,3,2],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := b1_3`mat[1,1] / e1`mat[1,1];
    e3 := f2_t - 1/k1_3 * u2_1 * d2_1;

    assert e3 eq e3 * e3;
    
    //e4
    e4 := Tensor(act, e3, [id,s]);
    assert e4 eq e4*e4;
    
    //e5
    f4_t := Tensor(act, e4, [id,t]);
    d4_3 := e3 * LocalisedLLDown(B,[2,3,2,1,2],[1,1,1,0,0]) * f4_t;
    u4_3 := f4_t * LocalisedLLUp(B,[2,3,2,1,2],[1,1,1,0,0]) * e3;
    b3_5 := d4_3 * u4_3;
    k3_5 := b3_5`mat[1,1] / e3`mat[1,1];
    e5 := f4_t - 1/k3_5 * u4_3 * d4_3;
    
    //e6
    f5_u := Tensor(act, e5, [id,u]);
    d5_4 := e4 * Tensor(act, Braid(B,3,2)`stdmor, BSId(B,1)`stdmor) * Tensor(act, BSId(B,[3,2])`stdmor, Braid(B,1,3)`stdmor) * LocalisedLLDown(B,[2,3,2,1,2,3],[1,1,1,1,0,0]) * f5_u;
    u5_4 := f5_u * LocalisedLLUp(B,[2,3,2,1,2,3],[1,1,1,1,0,0]) * Tensor(act, BSId(B,[3,2])`stdmor, Braid(B,3,1)`stdmor) * Tensor(act, Braid(B,2,3)`stdmor, BSId(B,1)`stdmor) * e4;
    b4_6 := d5_4 * u5_4;
    k4_6 := b4_6`mat[1,1] / e4`mat[1,1];
    e6 := f5_u - 1/k4_6 * u5_4 * d5_4;
    
    //Now we check the positive root:
    //The positive root should be (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3; Check:    
    root := (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3;
    assert Matrix(Mult(B,1)`stdmor * Tensor(act, BSId(B,1)`stdmor, root*BSId(B,1)`stdmor) * Comult(B,1)`stdmor) eq Matrix(BSId(B,1)`stdmor);
    assert Matrix(Mult(B,2)`stdmor * Tensor(act, BSId(B,2)`stdmor, root*BSId(B,2)`stdmor) * Comult(B,2)`stdmor) eq Matrix(BSId(B,2)`stdmor);
    assert Matrix(Mult(B,3)`stdmor * Tensor(act, BSId(B,3)`stdmor, root*BSId(B,3)`stdmor) * Comult(B,3)`stdmor) eq Matrix(BSId(B,3)`stdmor);
    
    //We compute the partial trace and dimension:
    partial5 :=  Tensor(act, e5, Cap(B,3)`stdmor) * Tensor(act, e6, root^3*(BSId(B,3)`stdmor)) * Tensor(act, e5, Cup(B,3)`stdmor);

    partial4 :=  Tensor(act, e4, Cap(B,2)`stdmor) * Tensor(act, partial5, BSId(B,2)`stdmor) *  Tensor(act, e4, Cup(B,2)`stdmor);

    partial3 :=  Tensor(act, e3, Cap(B,1)`stdmor) * Tensor(act, partial4, BSId(B,1)`stdmor) * Tensor(act, e3, Cup(B,1)`stdmor);

    dtop := LocalisedLLDown(B,[2,3,2,2,3,2],[1,1,1,0,0,0]);
    dbot := LocalisedLLUp(B,[2,3,2,2,3,2],[1,1,1,0,0,0]);
    
    trace_d := dtop * Tensor(act, e3, root^3*e3) * dbot;
    dim_d := trace_d`mat[1,1] / trace_d`mat[1,1];
    
    trace_w := dtop * Tensor(act, partial3, e3) * dbot; 
    
    dim_w := trace_w`mat[1,1] / trace_d`mat[1,1];
    
    assert dim_w eq -1;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("All assertions correct. The dimension of ew is %o. Total time for the calculation took %o, used space was %o.", dim_w, T, S);
end procedure;

//Continue with Case H4; a-value of 2; d = 13, w = d2143;
procedure H4_complete()
    ResetMaximumMemoryUsage();
    T := Time();

    //Change the construction of BSCat.m such that we can create it for H4
    //AttachSpec("ASLoc.spec");
    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");

    //The cartan matrix lives over a cyclotomic field including phi
    f := BaseRing(carH4);
    FR := RationalFunctionField(f,Rank(W));

    //We can construct the right BSCategory with the new field
    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    FA := B`FAct;

    act := function(w)
        return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;
    v := W.4;

    //Create idempotents:
    e1 := BSId(B,3)`stdmor;
    assert e1 eq e1*e1;

    e2 := Tensor(act,e1,[id,s]);
    assert e2 eq e2*e2;

    e3 := Tensor(act,e2,[id,t]);
    assert e3 eq e3*e3;

    //Only case with more summands, luckily no rex moves
    f3_s := Tensor(act, e3, [id,s]);
    d3_2 := LocalisedLLDown(B,[3,1,2,1],[1,1,0,0]);
    u3_2 := LocalisedLLUp(B,[3,1,2,1],[1,1,0,0]);
    b2_4 := e2 * d3_2 * f3_s * u3_2 * e2;
    k2_4 := Matrix(b2_4)[1,1] / Matrix(e2)[1,1];
    //k2_4 := -f.1;
    e4 := f3_s - 1/k2_4 * f3_s * u3_2 * e2 * d3_2 * f3_s;
    assert e4 eq e4*e4;

    e5 := Tensor(act,e4,[id,v]);
    assert e5 eq e5*e5;

    e6 := Tensor(act,e5,[id,u]);
    assert e6 eq e6*e6;

    //positive root:
    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
    assert Matrix(Mult(B,1)`stdmor * Tensor(act, BSId(B,1)`stdmor, root*BSId(B,1)`stdmor) * Comult(B,1)`stdmor) eq Matrix(BSId(B,1)`stdmor);
    assert Matrix(Mult(B,2)`stdmor * Tensor(act, BSId(B,2)`stdmor, root*BSId(B,2)`stdmor) * Comult(B,2)`stdmor) eq Matrix(BSId(B,2)`stdmor);
    assert Matrix(Mult(B,3)`stdmor * Tensor(act, BSId(B,3)`stdmor, root*BSId(B,3)`stdmor) * Comult(B,3)`stdmor) eq Matrix(BSId(B,3)`stdmor);
    assert Matrix(Mult(B,4)`stdmor * Tensor(act, BSId(B,4)`stdmor, root*BSId(B,4)`stdmor) * Comult(B,4)`stdmor) eq Matrix(BSId(B,4)`stdmor);

    //partial trace: We form 4 cup and cap loops around ew to get to ed.
    ddtop312143 := LocalisedLLDown(B,[3,1,2,1,4,3,3,4,1,2],[1,1,1,1,1,1,1,1,1,1]);
    ddbot312143 := LocalisedLLUp(B,[3,1,2,1,4,3,3,4,1,2],[1,1,1,1,1,1,1,1,1,1]);

    //Note, that here we have not normalized root^2. Therefore we need to divide by a scalar later
    dd312143 := ddtop312143 * (Tensor(act,e6,root^2*BSId(B,[3,4,1,2])`stdmor)) * ddbot312143; 
	
    //The trace and therefore the dimension of ew is then the result of the following diagram:
    dtop31 := (Braid(B,1,3) * ([1] cat Mult(B,3)) * (Braid(B,3,1) cat [3]) * ([3] cat Mult(B,1) cat [3]))`stdmor;
    dbot31 := (([3] cat Comult(B,1) cat [3]) * (Braid(B,1,3) cat [3]) * ([1] cat Comult(B,3)) * Braid(B,3,1))`stdmor;
    d31 := dtop31 * Tensor(act,dd312143,BSId(B,[1,3])`stdmor) * dbot31;
    
    //The unnormalized dimension of ed can be computed similarly:
    d := dtop31 * Tensor(act,e2,root^2*BSId(B,[1,3])`stdmor) * dbot31;

    //The dimension is then the quotient of the following:
    dimw := d31`mat[1,1]/d`mat[1,1];
    assert dimw eq f.1;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("All assertions correct. The dimension of ew is %o. Total time for the calculation took %o, used space was %o.", dimw, T, S);
end procedure;

//Continue with the longest case in type H3; a-value of 6; w = 1212132121, d = w3212;
procedure H3_long_complete()
    ResetMaximumMemoryUsage();
    T := Time();

    //Change the construction of BSCat.m such that we can create it for H3
    //AttachSpec("ASLoc.spec");
    carH3 := CartanMatrix("H3");
    W := CoxeterGroup(GrpFPCox, "H3");

    //The cartan matrix lives over a cyclotomic field including phi
    f := BaseRing(carH3);
    FR := RationalFunctionField(f,Rank(W));

    //We can construct the right BSCategory with the new field
    B := New(BSCat);
    B`C := carH3;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    FA := B`FAct;

    act := function(w)
        return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;
    
    e1 := BSId(B,1)`stdmor;
    //Decompose decomposes idempotents f = incl * proj and returns an error if f is not idempotent
    //This line is redundant, only at e3 it gets interesting
    //Using the function DecomposeIdem is an implicit assertion. If the map would not be idempotent it returns an error
    proj1, incl1 := DecomposeIdem(e1);

    e2 := Tensor(act,e1,[id,t]);
    proj2to1, incl1to2 := DecomposeIdem(e2);

    //fi_s is tensor product from ei with s
    //di_j goes down from fi_2 to ej; ui_j up; 
    //in b1_3 we compute the composition to get the coefficient k1_3
    //This then creates our new idempotent
    f2_s := Tensor(act, e2, [id,s]);
    d2_1 := e1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * f2_s;
    u2_1 := f2_s * LocalisedLLUp(B,[1,2,1],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := Matrix(b1_3)[1,1] / Matrix(e1)[1,1];
    //k1_3 := -f.1;
    e3 := f2_s - 1/k1_3 * u2_1 * d2_1;
    proj3to1, incl1to3 := DecomposeIdem(e3);
    e3red := proj3to1 * e3 * incl1to3;

    //From now on work with a reduced form e3red. Get back old form with
    //assert e3 eq incl1to3 * e3red * proj3to1;
    
    //e4:
    f3_t := Tensor(act, e3red, [id,t]);
    incl3_t := Tensor(act, incl1to3, [id,t]);
    proj3_t := Tensor(act, proj3to1, [id,t]);
    d3_2 := e2 * LocalisedLLDown(B,[1,2,1,2],[1,1,0,0]) * incl3_t * f3_t;
    u3_2 := f3_t * proj3_t * LocalisedLLUp(B,[1,2,1,2],[1,1,0,0]) * e2;
    b2_4 := d3_2 * u3_2;
    k2_4 := Matrix(b2_4)[1,1] / Matrix(e2)[1,1];
    //k2_4 := -1;
    e4 := f3_t - 1/k2_4 * u3_2 * d3_2;
    //e4 eq e4*e4;
    proj4to3, incl3to4 := DecomposeIdem(e4);
    e4red := proj4to3 * e4 * incl3to4;
    
    //If one prefers a 16x16 matrix one can construct the idempotemt via
    //Tensor(act, incl1to3, [id,t]) * incl3to4 * e4red * proj4to3 * Tensor(act, proj3to1, [id,t]);
    //I.e. we have to stack the inclusions and projections
    incl1to4 := Tensor(act, incl1to3, [id,t]) * incl3to4;
    proj4to1 := proj4to3 * Tensor(act, proj3to1, [id,t]);

    //e5:
    f4_s := Tensor(act, e4red, [id,s]);
    d4_3 := e3red * proj3to1 * (Tensor(act, e2, LocalisedLLDown(B,[1,2,1],[1,0,0]))) * Tensor(act, incl1to4, [id,s]) * f4_s;
    u4_3 := f4_s * Tensor(act, proj4to1, [id,s]) * Tensor(act, e2, LocalisedLLUp(B,[1,2,1],[1,0,0])) * incl1to3 * e3red;
    b3_5 := d4_3 * u4_3;
    k3_5 := Matrix(b3_5)[1,1] / Matrix(e3red)[1,1];
    //k3_5 := -f.1 +1;
    e5 := f4_s - 1/k3_5 * u4_3 * e3red * d4_3;
    proj5to4, incl4to5 := DecomposeIdem(e5);

    e5red := proj5to4 * e5 * incl4to5;
    incl1to5 := Tensor(act, incl1to4, [id,s]) * incl4to5;
    proj5to1 := proj5to4 * Tensor(act, proj4to1, [id,s]);
    incl3to5 := Tensor(act, incl3to4, [id,s]) * incl4to5;
    proj5to3 := proj5to4 * Tensor(act, proj4to3, [id,s]);

    //e6:
    e6 := Tensor(act, e5red, [id,u]);
    proj6to5, incl5to6 := DecomposeIdem(e6);
    e6red := proj6to5 * e6 * incl5to6;

    incl1to6 := Tensor(act, incl1to5, [id,u]) * incl5to6;
    proj6to1 := proj6to5 * Tensor(act, proj5to1, [id,u]);
    incl4to6 := Tensor(act, incl4to5, [id,u]) * incl5to6;
    proj6to4 := proj6to5 * Tensor(act, proj5to4, [id,u]);

    //e7:
    //From here on out we need braids:
    f6_t := Tensor(act, e6red, [id,t]);
    br6to5 := (Braid(B,1,2) cat [3,2])`stdmor;
    br5from6 := (Braid(B,2,1))`stdmor;
    br5to6 := (Braid(B,1,2))`stdmor;
    br6from5 := (Braid(B,2,1) cat [3,2])`stdmor;

    d6_5 := e5red * proj5to1 * br5from6 * LocalisedLLDown(B,[2,1,2,1,2,3,2],[1,1,1,1,1,0,0]) * br6to5 * Tensor(act, incl1to6, [id,t]) * f6_t;
    u6_5 := f6_t * Tensor(act, proj6to1, [id,t]) * br6from5 * LocalisedLLUp(B,[2,1,2,1,2,3,2],[1,1,1,1,1,0,0]) * br5to6 * incl1to5 * e5red;

    b5_7 := d6_5 * u6_5;
    k5_7 := Matrix(b5_7)[1,1] / Matrix(e5red)[1,1];
    //k5_7 := -1;
    e7 := f6_t - 1/k5_7 * u6_5 * d6_5;
    proj7to6, incl6to7 := DecomposeIdem(e7);
    e7red := proj7to6 * e7 * incl6to7;
    
    incl1to7 := Tensor(act, incl1to6, [id,t]) * incl6to7;
    proj7to1 := proj7to6 * Tensor(act, proj6to1, [id,t]);
    incl5to7 := Tensor(act, incl5to6, [id,t]) * incl6to7;
    proj7to5 := proj7to6 * Tensor(act, proj6to5, [id,t]);
    incl4to7 := Tensor(act, incl4to6, [id,t]) * incl6to7;
    proj7to4 := proj7to6 * Tensor(act, proj6to4, [id,t]);

    //e8:
    f7_s := Tensor(act, e7red, [id,s]);
    //We include e7red into e4\otimes 132 so that we can braid in the end; then tensor with s, apply light leave, braid back and project back onto e7red
    d7_6 := proj6to4 * Tensor(act, e4red, Braid(B,3,1)`stdmor) * Tensor(act, e4red, LocalisedLLDown(B,[3,1,2,1],[1,1,0,0])) * Tensor(act, Tensor(act, Tensor(act, e4red, Braid(B,1,3)`stdmor), [id,t]) * incl4to7 ,[id,s]) * f7_s;                     
    u7_6 := f7_s * Tensor(act, proj7to4 * Tensor(act, Tensor(act, e4red, Braid(B,3,1)`stdmor), [id,t]),[id,s]) * Tensor(act, e4red, LocalisedLLUp(B,[3,1,2,1],[1,1,0,0])) * Tensor(act, e4red, Braid(B,1,3)`stdmor) * incl4to6;
    b6_8 := d7_6 * u7_6;
    k6_8 := Matrix(b6_8)[1,1] / Matrix(e6red)[1,1];
    //k6_8 := -f.1;
    e8 := f7_s - 1/k6_8 * u7_6 * d7_6;
    proj8to7, incl7to8 := DecomposeIdem(e8);
    e8red := proj8to7 * e8 * incl7to8;
    incl6to8 := Tensor(act, incl6to7, [id,s]) * incl7to8;
    proj8to6 := proj8to7 * Tensor(act, proj7to6, [id,s]);
    incl1to8 := Tensor(act, incl1to7, [id,s]) * incl7to8;
    proj8to1 := proj8to7 * Tensor(act, proj7to1, [id,s]);
    incl5to8 := Tensor(act, incl5to7, [id,s]) * incl7to8;
    proj8to5 := proj8to7 * Tensor(act, proj7to5, [id,s]);
    incl4to8 := Tensor(act, incl4to7, [id,s]) * incl7to8;
    proj8to4 := proj8to7 * Tensor(act, proj7to4, [id,s]);

    //e9:
    //f8_t := Tensor(act, e8red, [id,t]);
    d8_7 := proj7to6 * Tensor(act, e6red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl6to8, [id,t]);
    u8_7 := Tensor(act, proj8to6, [id,t]) * Tensor(act, e6red, LocalisedLLUp(B,[2,1,2],[1,0,0])) * incl6to7;
    b7_9 := d8_7 * u8_7;
    k7_9 := Matrix(b7_9)[1,1] / Matrix(e7red)[1,1];
    //k7_9 := -1; 
    e9 := Tensor(act, e8red, [id,t]) - 1/k7_9 * u8_7 * d8_7;
    proj9to8, incl8to9 := DecomposeIdem(e9);
    e9red := proj9to8 * e9 * incl8to9;
    incl7to9 := Tensor(act, incl7to8, [id,t]) * incl8to9;
    proj9to7 := proj9to8 * Tensor(act, proj8to7, [id,t]);
    incl1to9 := Tensor(act, incl1to8, [id,t]) * incl8to9;
    proj9to1 := proj9to8 * Tensor(act, proj8to1, [id,t]);
    incl5to9 := Tensor(act, incl5to8, [id,t]) * incl8to9;
    proj9to5 := proj9to8 * Tensor(act, proj8to5, [id,t]);
    incl4to9 := Tensor(act, incl4to8, [id,t]) * incl8to9;
    proj9to4 := proj9to8 * Tensor(act, proj8to4, [id,t]);

    //e10
    //f9_s := Tensor(act, e9red, [id,s]);
    d9_8 := proj8to7 * Tensor(act, e7red, LocalisedLLDown(B,[1,2,1],[1,0,0])) * Tensor(act, incl7to9, [id,s]);
    u9_8 := Tensor(act, proj9to7, [id,s]) * Tensor(act, e7red, LocalisedLLUp(B,[1,2,1],[1,0,0])) * incl7to8;
    b8_10 := d9_8 * u9_8;
    k8_10 := Matrix(b8_10)[1,1] / Matrix(e8red)[1,1];
    //k8_10 := -f.1+1;
    e10 := Tensor(act, e9red, [id,s]) - 1/k8_10 * u9_8 * d9_8;
    proj10to9, incl9to10 := DecomposeIdem(e10);
    e10red := proj10to9 * e10 * incl9to10;
    incl5to10 := Tensor(act, incl5to9, [id,s]) * incl9to10;
    proj10to5 := proj10to9 * Tensor(act, proj9to5, [id,s]);
    incl4to10 := Tensor(act, incl4to9, [id,s]) * incl9to10;
    proj10to4 := proj10to9 * Tensor(act, proj9to4, [id,s]);
    incl1to10 := Tensor(act, incl1to9, [id,s]) * incl9to10;
    proj10to1 := proj10to9 * Tensor(act, proj9to1, [id,s]);
    incl8to10 := Tensor(act, incl8to9, [id,s]) * incl9to10;
    proj10to8 := proj10to9 * Tensor(act, proj9to8, [id,s]);

    //ex
    br9to8 := (([2,1,2,1,3,2] cat Braid(B,3,1) cat [2]) * ([2,1,2,1] cat Braid(B,2,3) cat[1,2]) * (Braid(B,1,2) cat [3,2,1,2]))`stdmor;
    br9from8 := ((Braid(B,2,1) cat [3,2,1,2]) * ([2,1,2,1] cat Braid(B,3,2) cat[1,2]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2]))`stdmor;
    br8from9 :=  ((Braid(B,2,1) cat [3,2,1]) * ([2,1,2,1] cat Braid(B,3,2) cat[1]) * ([2,1,2,1,3,2] cat Braid(B,1,3)))`stdmor;
    br8to9 := (([2,1,2,1,3,2] cat Braid(B,3,1)) * ([2,1,2,1] cat Braid(B,2,3) cat[1]) * (Braid(B,1,2) cat [3,2,1]))`stdmor;

    dx_8 := proj8to1 * br8from9 * LocalisedLLDown(B,[2,1,2,1,3,2,1,3,2,3],[1,1,1,1,1,1,1,1,0,0]) * Tensor(act, br9to8 * incl1to9, [id,u]);
    ux_8 := Tensor(act, proj9to1 * br9from8, [id,u]) * LocalisedLLUp(B,[2,1,2,1,3,2,1,3,2,3],[1,1,1,1,1,1,1,1,0,0]) * br8to9 * incl1to8;

    b8_x := dx_8 * ux_8;
    k8_x := Matrix(b8_x)[1,1] / Matrix(e8red)[1,1];
    //k8_x := -1;
    ex := Tensor(act, e9red, [id,u]) - 1/k8_x * ux_8 * dx_8;
    projxto9, incl9tox := DecomposeIdem(ex);
    exred := projxto9 * ex * incl9tox;
    incl1tox := Tensor(act, incl1to9, [id,u]) * incl9tox;
    projxto1 := projxto9 * Tensor(act, proj9to1, [id,u]);

    //e11:
    e11 := Tensor(act, e10red, [id,u]);
    proj11to10, incl10to11 := DecomposeIdem(e11);
    e11red := proj11to10 * e11 * incl10to11;
    incl9to11 := Tensor(act, incl9to10, [id,u]) * incl10to11;
    proj11to9 := proj11to10 * Tensor(act, proj10to9, [id,u]);
    incl5to11 := Tensor(act, incl5to10, [id,u]) * incl10to11;
    proj11to5 := proj11to10 * Tensor(act, proj10to5, [id,u]);
    incl4to11 := Tensor(act, incl4to10, [id,u]) * incl10to11;
    proj11to4 := proj11to10 * Tensor(act, proj10to4, [id,u]);
    incl1to11 := Tensor(act, incl1to10, [id,u]) * incl10to11;
    proj11to1 := proj11to10 * Tensor(act, proj10to1, [id,u]);

    //Check if going from x to 11 gives same result:
    brx1to11 := ([1,2,1,2,1,3,2,1,2] cat Braid(B,3,1))`stdmor;
    brx1from11 := ([1,2,1,2,1,3,2,1,2] cat Braid(B,1,3))`stdmor;
    assert e11 eq proj11to9 * Tensor(act, e9red, Braid(B,3,1)`stdmor) * Tensor(act, incl9tox, [id,s]) * Tensor(act, projxto9, [id,s]) * Tensor(act, e9red, Braid(B,1,3)`stdmor) * incl9to11;

    //e12:
    //For 12 we now have two summands. This is the most messy calculation
    br11to10 := Tensor(act, e4red, (([3] cat Braid(B,1,2) cat [3]) * (Braid(B,1,3) cat [2,1,2,1,3]))`stdmor);
    br10to11 := Tensor(act, e4red, (([3] cat Braid(B,1,2)) * (Braid(B,1,3) cat [2,1,2,1]))`stdmor);
    br11from10 := Tensor(act, e4red, ((Braid(B,3,1) cat [2,1,2,1,3]) * ([3] cat Braid(B,2,1) cat [3]))`stdmor);
    br10from11 := Tensor(act, e4red, ((Braid(B,3,1) cat [2,1,2,1]) * ([3] cat Braid(B,2,1)))`stdmor);

    d11_10 := proj10to4 * br10from11 *  Tensor(act, e4red, LocalisedLLDown(B,[3,2,1,2,1,2,3,2],[1,1,1,1,1,1,0,0]))  * Tensor(act, br11to10 * incl4to11, [id,t]);
    u11_10 := Tensor(act, proj11to4 * br11from10, [id,t]) * Tensor(act, e4red, LocalisedLLUp(B,[3,2,1,2,1,2,3,2],[1,1,1,1,1,1,0,0])) * br10to11 * incl4to10;

    b10_12 := d11_10 * u11_10;
    k10_12 := Matrix(b10_12)[1,1] / Matrix(e10red)[1,1];
    //k10_12 := -1;

    br11tox := (([2,1,2,1,3,2,1] cat Braid(B,3,2) cat [1]) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2] cat Braid(B,1,3)) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2,1,3]) * (Braid(B,1,2) cat [3,2,1,2,1,3]))`stdmor;
    brxto11 := (([2,1,2,1,3,2,1] cat Braid(B,3,2)) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2,3]) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2,3]) * (Braid(B,1,2) cat [3,2,1,2,3]))`stdmor;
    br11fromx := (((Braid(B,2,1) cat [3,2,1,2,1,3]) * [2,1,2,1] cat Braid(B,3,2) cat [1,2,1,3]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2] cat Braid(B,3,1)) * ([2,1,2,1,3,2,1] cat Braid(B,2,3) cat [1]))`stdmor;
    brxfrom11 := (((Braid(B,2,1) cat [3,2,1,2,3]) * [2,1,2,1] cat Braid(B,3,2) cat [1,2,3]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2,3]) * ([2,1,2,1,3,2,1] cat Braid(B,2,3)))`stdmor;

    d11_x := projxto1 * brxfrom11 *  LocalisedLLDown(B,[2,1,2,1,3,2,1,2,3,2,1,2],[1,1,1,1,1,1,1,1,1,1,0,0])  * Tensor(act, br11tox * incl1to11, [id,t]);
    u11_x := Tensor(act, proj11to1 * br11fromx, [id,t]) * LocalisedLLUp(B,[2,1,2,1,3,2,1,2,3,2,1,2],[1,1,1,1,1,1,1,1,1,1,0,0]) * brxto11 * incl1tox;

    bx_12 := d11_x * u11_x;
    kx_12 := Matrix(bx_12)[1,1] / Matrix(exred)[1,1];
    //kx_12 := -f.1;

    e12 := Tensor(act, e11red, [id,t]) - 1/k10_12 * u11_10 * d11_10 - 1/kx_12 * u11_x * d11_x;
    proj12to11, incl11to12 := DecomposeIdem(e12);
    e12red := proj12to11 * e12 * incl11to12;
    incl10to12 := Tensor(act, incl10to11, [id,t]) * incl11to12;
    proj12to10 := proj12to11 * Tensor(act, proj11to10, [id,t]);
    incl9to12 := Tensor(act, incl9to11, [id,t]) * incl11to12;
    proj12to9 := proj12to11 * Tensor(act, proj11to9, [id,t]);
    incl1to12 := Tensor(act, incl1to11, [id,t]) * incl11to12;
    proj12to1 := proj12to11 * Tensor(act, proj11to1, [id,t]);

    //Last rex moves in e13:
    br12to11 := Tensor(act, e9red, (Braid(B,1,3) cat [2])`stdmor);
    br11to12 := Tensor(act, e9red, (Braid(B,1,3))`stdmor);
    br12from11 := Tensor(act, e9red, (Braid(B,3,1) cat [2])`stdmor);
    br11from12 := Tensor(act, e9red, (Braid(B,3,1))`stdmor);

    d12_11 := proj11to9 * br11from12 *  Tensor(act, e9red, LocalisedLLDown(B,[3,1,2,1],[1,1,0,0])) * Tensor(act, br12to11 * incl9to12, [id,s]);
    u12_11 := Tensor(act, proj12to9 * br12from11, [id,s]) * Tensor(act, e9red, LocalisedLLUp(B,[3,1,2,1],[1,1,0,0])) * br11to12 * incl9to11;

    b11_13 := d12_11 * u12_11;
    k11_13 := Matrix(b11_13)[1,1] / Matrix(e11red)[1,1];
    //k11_13 := -1;

    e13 := Tensor(act, e12red, [id,s]) - 1/k11_13 * u12_11 * d12_11;
    proj13to12, incl12to13 := DecomposeIdem(e13);
    e13red := proj13to12 * e13 * incl12to13;
    incl11to13 := Tensor(act, incl11to12, [id,s]) * incl12to13;
    proj13to11 := proj13to12 * Tensor(act, proj12to11, [id,s]);
    incl1to13 := Tensor(act, incl1to12, [id,s]) * incl12to13;
    proj13to1 := proj13to12 * Tensor(act, proj12to1, [id,s]);

    //Last idempotent; e14:
    d13_12 := proj12to11 * Tensor(act, e11red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl11to13, [id,t]);
    u13_12 := Tensor(act, proj13to11, [id,t]) * Tensor(act, e11red, LocalisedLLUp(B,[2,1,2],[1,0,0])) * incl11to12;

    b12_14 := d13_12 * u13_12;
    k12_14 := Matrix(b12_14)[1,1] / Matrix(e12red)[1,1];
    //k12_14 := -f.1 + 1;
    e14 := Tensor(act, e13red, [id,t]) - 1/k12_14 * u13_12 * d13_12;
    proj14to13, incl13to14 := DecomposeIdem(e14);
    e14red := proj14to13 * e14 * incl13to14;
    incl1to14 := Tensor(act, incl1to13, [id,t]) * incl13to14;
    proj14to1 := proj14to13 * Tensor(act, proj13to1, [id,t]);

    ////Time
    T1 := Time(T);
    S := GetMaximumMemoryUsage();
    //ShowMemoryUsage();
    ResetMaximumMemoryUsage();

    Sprintf("The computation of all 14 idempotents took %o seconds and used %o of space", T1, S);

    //positive root:
    root := (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3;
    assert Matrix(Mult(B,1)`stdmor * Tensor(act, BSId(B,1)`stdmor, root*BSId(B,1)`stdmor) * Comult(B,1)`stdmor) eq Matrix(BSId(B,1)`stdmor);
    assert Matrix(Mult(B,2)`stdmor * Tensor(act, BSId(B,2)`stdmor, root*BSId(B,2)`stdmor) * Comult(B,2)`stdmor) eq Matrix(BSId(B,2)`stdmor);
    assert Matrix(Mult(B,3)`stdmor * Tensor(act, BSId(B,3)`stdmor, root*BSId(B,3)`stdmor) * Comult(B,3)`stdmor) eq Matrix(BSId(B,3)`stdmor);

    //Compute a mirror e10; This is done for speed reasons for the trace. The calculations are the same as above for e10
    //eflip1
    eflip1 := BSId(B,1)`stdmor;

    //eflip2
    eflip2 := Tensor(act, [id,t], eflip1);
    projflip2to1, inclflip1to2 := DecomposeIdem(eflip2);

    //eflip3
    fflips_2 := Tensor(act, [id,s], eflip2);
    dflip2_1 := eflip1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * fflips_2;
    uflip2_1 := fflips_2 * LocalisedLLUp(B,[1,2,1],[1,0,0]) * eflip1;
    //bflip1_3 := dflip2_1 * uflip2_1;
    //kflip1_3 := Matrix(bflip1_3)[1,1] / Matrix(eflip1)[1,1];
    kflip1_3 := -f.1;
    eflip3 := fflips_2 - 1/kflip1_3 * uflip2_1 * dflip2_1;
    projflip3to1, inclflip1to3 := DecomposeIdem(eflip3);
    eflip3red := projflip3to1 * eflip3 * inclflip1to3;

    //eflip4
    fflipt_3 := Tensor(act, [id,t], eflip3red);
    inclflip3_t := Tensor(act, [id,t], inclflip1to3);
    projflip3_t := Tensor(act, [id,t], projflip3to1);
    dflip3_2 := eflip2 * LocalisedLLDown(B,[2,1,2,1],[1,0,0,1]) * inclflip3_t * fflipt_3;
    uflip3_2 := fflipt_3 * projflip3_t * LocalisedLLUp(B,[2,1,2,1],[1,0,0,1]) * eflip2;
    //bflip2_4 := dflip3_2 * uflip3_2;
    //kflip2_4 := Matrix(bflip2_4)[1,1] / Matrix(eflip2)[1,1];
    kflip2_4 := -1;
    eflip4 := fflipt_3 - 1/kflip2_4 * uflip3_2 * dflip3_2;
    projflip4to3, inclflip3to4 := DecomposeIdem(eflip4);
    eflip4red := projflip4to3 * eflip4 * inclflip3to4;
    inclflip1to4 := Tensor(act, [id,t], inclflip1to3) * inclflip3to4;
    projflip4to1 := projflip4to3 * Tensor(act, [id,t], projflip3to1);

    //eflip5
    fflips_4 := Tensor(act, [id,s], eflip4red);
    dflip4_3 := eflip3red * projflip3to1 * (Tensor(act, LocalisedLLDown(B,[1,2,1],[1,0,0]), eflip2)) * Tensor(act, [id,s], inclflip1to4) * fflips_4;
    uflip4_3 := fflips_4 * Tensor(act, [id,s], projflip4to1) * Tensor(act, LocalisedLLUp(B,[1,2,1],[1,0,0]), eflip2) * inclflip1to3 * eflip3red;
    //bflip3_5 := dflip4_3 * uflip4_3;
    //kflip3_5 := Matrix(bflip3_5)[1,1] / Matrix(eflip3red)[1,1];
    kflip3_5 := -f.1 +1;
    eflip5 := fflips_4 - 1/kflip3_5 * uflip4_3 * eflip3red * dflip4_3;
    projflip5to4, inclflip4to5 := DecomposeIdem(eflip5);
    eflip5red := projflip5to4 * eflip5 * inclflip4to5;
    inclflip1to5 := Tensor(act, [id,s], inclflip1to4) * inclflip4to5;
    projflip5to1 := projflip5to4 * Tensor(act, [id,s], projflip4to1);
    inclflip3to5 := Tensor(act, [id,s], inclflip3to4) * inclflip4to5;
    projflip5to3 := projflip5to4 * Tensor(act, [id,s], projflip4to3);

    //eflip6
    eflip6 := Tensor(act, [id,u], eflip5red);
    projflip6to5, inclflip5to6 := DecomposeIdem(eflip6);
    eflip6red := projflip6to5 * eflip6 * inclflip5to6;
    inclflip1to6 := Tensor(act, [id,u], inclflip1to5) * inclflip5to6;
    projflip6to1 := projflip6to5 * Tensor(act, [id,u], projflip5to1);
    inclflip4to6 := Tensor(act, [id,u], inclflip4to5) * inclflip5to6;
    projflip6to4 := projflip6to5 * Tensor(act, [id,u], projflip5to4);

    //From here on out we need braids:
    fflipt_6 := Tensor(act, [id,t], eflip6red);
    brflip6to5 := ([2,3] cat Braid(B,1,2))`stdmor;
    brflip5from6 := (Braid(B,2,1))`stdmor;
    brflip5to6 := (Braid(B,1,2))`stdmor;
    brflip6from5 := ([2,3] cat Braid(B,2,1))`stdmor;

    dflip6_5 := eflip5red * projflip5to1 * brflip5from6 * LocalisedLLDown(B,[2,3,2,1,2,1,2],[1,0,0,1,1,1,1]) * brflip6to5 * Tensor(act, [id,t], inclflip1to6) * fflipt_6;
    uflip6_5 := fflipt_6 * Tensor(act, [id,t], projflip6to1) * brflip6from5 * LocalisedLLUp(B,[2,3,2,1,2,1,2],[1,0,0,1,1,1,1]) * brflip5to6 * inclflip1to5 * eflip5red;

    //bflip5_7 := dflip6_5 * uflip6_5;
    //kflip5_7 := Matrix(bflip5_7)[1,1] / Matrix(eflip5red)[1,1];
    kflip5_7 := -1;
    eflip7 := fflipt_6 - 1/kflip5_7 * uflip6_5 * dflip6_5;
    projflip7to6, inclflip6to7 := DecomposeIdem(eflip7);
    eflip7red := projflip7to6 * eflip7 * inclflip6to7;
    inclflip1to7 := Tensor(act, [id,t], inclflip1to6) * inclflip6to7;
    projflip7to1 := projflip7to6 * Tensor(act, [id,t], projflip6to1);
    inclflip5to7 := Tensor(act, [id,t], inclflip5to6) * inclflip6to7;
    projflip7to5 := projflip7to6 * Tensor(act, [id,t], projflip6to5);
    inclflip4to7 := Tensor(act, [id,t], inclflip4to6) * inclflip6to7;
    projflip7to4 := projflip7to6 * Tensor(act, [id,t], projflip6to4);

    //eflip8:
    fflips_7 := Tensor(act, [id,s], eflip7red);
    //We include e7red into e4\otimes 132 so that we can braid in the end; then tensor with s, apply light leave, braid back and project back onto e7red
    dflip7_6 := projflip6to4 * Tensor(act, Braid(B,1,3)`stdmor, eflip4red) * Tensor(act, LocalisedLLDown(B,[1,2,1,3],[1,0,0,1]), eflip4red) * Tensor(act ,[id,s], Tensor(act, [id,t], Tensor(act, Braid(B,3,1)`stdmor, eflip4red)) * inclflip4to7) * fflips_7;                     
    uflip7_6 := fflips_7 * Tensor(act ,[id,s], projflip7to4 * Tensor(act, [id,t], Tensor(act, Braid(B,1,3)`stdmor, eflip4red))) * Tensor(act, LocalisedLLUp(B,[1,2,1,3],[1,0,0,1]), eflip4red) * Tensor(act, Braid(B,3,1)`stdmor, eflip4red) * inclflip4to6;
    //bflip6_8 := dflip7_6 * uflip7_6;
    //kflip6_8 := Matrix(bflip6_8)[1,1] / Matrix(eflip6red)[1,1];
    kflip6_8 := -f.1;
    eflip8 := fflips_7 - 1/kflip6_8 * uflip7_6 * dflip7_6;
    projflip8to7, inclflip7to8 := DecomposeIdem(eflip8);
    eflip8red := projflip8to7 * eflip8 * inclflip7to8;
    inclflip6to8 := Tensor(act, [id,s], inclflip6to7) * inclflip7to8;
    projflip8to6 := projflip8to7 * Tensor(act, [id,s], projflip7to6);
    inclflip1to8 := Tensor(act, [id,s], inclflip1to7) * inclflip7to8;
    projflip8to1 := projflip8to7 * Tensor(act, [id,s], projflip7to1);
    inclflip5to8 := Tensor(act, [id,s], inclflip5to7) * inclflip7to8;
    projflip8to5 := projflip8to7 * Tensor(act, [id,s], projflip7to5);

    //eflip9:
    fflipt_8 := Tensor(act, [id,t], eflip8red);
    dflip8_7 := projflip7to6 * Tensor(act, LocalisedLLDown(B,[2,1,2],[1,0,0]), eflip6red) * Tensor(act, [id,t], inclflip6to8);
    uflip8_7 := Tensor(act, [id,t], projflip8to6) * Tensor(act, LocalisedLLUp(B,[2,1,2],[1,0,0]), eflip6red) * inclflip6to7;
    bflip7_9 := dflip8_7 * uflip8_7;
    kflip7_9 := Matrix(bflip7_9)[1,1] / Matrix(eflip7red)[1,1];
    //k7_9 := -1; 
    eflip9 := Tensor(act, [id,t], eflip8red) - 1/kflip7_9 * uflip8_7 * dflip8_7;
    projflip9to8, inclflip8to9 := DecomposeIdem(eflip9);
    eflip9red := projflip9to8 * eflip9 * inclflip8to9;
    inclflip7to9 := Tensor(act, [id,t], inclflip7to8) * inclflip8to9;
    projflip9to7 := projflip9to8 * Tensor(act, [id,t], projflip8to7);
    inclflip1to9 := Tensor(act, [id,t], inclflip1to8) * inclflip8to9;
    projflip9to1 := projflip9to8 * Tensor(act, [id,t], projflip8to1);
    inclflip5to9 := Tensor(act, [id,t], inclflip5to8) * inclflip8to9;
    projflip9to5 := projflip9to8 * Tensor(act, [id,t], projflip8to5);

    //eflip10
    fflips_9 := Tensor(act, [id,s], eflip9red);
    dflip9_8 := projflip8to7 * Tensor(act, LocalisedLLDown(B,[1,2,1],[1,0,0]), eflip7red) * Tensor(act, [id,s], inclflip7to9);
    uflip9_8 := Tensor(act, [id,s], projflip9to7) * Tensor(act, LocalisedLLUp(B,[1,2,1],[1,0,0]), eflip7red) * inclflip7to8;
    //bflip8_10 := dflip9_8 * uflip9_8;
    //kflip8_10 := Matrix(bflip8_10)[1,1] / Matrix(eflip8red)[1,1];
    kflip8_10 := -f.1+1;
    eflip10 := Tensor(act, [id,s], eflip9red) - 1/kflip8_10 * uflip9_8 * dflip9_8;
    projflip10to9, inclflip9to10 := DecomposeIdem(eflip10);
    eflip10red := projflip10to9 * eflip10 * inclflip9to10;
    inclflip5to10 := Tensor(act, [id,s], inclflip5to9) * inclflip9to10;
    projflip10to5 := projflip10to9 * Tensor(act, [id,s], projflip9to5);
    inclflip1to10 := Tensor(act, [id,s], inclflip1to9) * inclflip9to10;
    projflip10to1 := projflip10to9 * Tensor(act, [id,s], projflip9to1);

    //Now the computation of the trace
    //We build the Light Leave maps step by step. From t1 on top and b1 on bottom to t10 and b10. 
    //The middle term e10 \otimes root^6 * eflip10 is the biggest matrix. We would like to multiply such a big matrix with smaller ones
    middle := Tensor(act, e10red, root^6*eflip10red);

    //The goal is to construct the maps e14 -> e10 x eflip10 -> e14 as in the document

    //Top maps; we simplify them step by step
    t1 := Tensor(act, proj10to9, eflip9red) * Tensor(act, e9red, Tensor(act, Mult(B,1)`stdmor, eflip9red)) * Tensor(act, incl9to10, inclflip9to10);
    b1 := Tensor(act, proj10to9, projflip10to9) * Tensor(act, e9red, Tensor(act, Comult(B,1)`stdmor, eflip9red)) * Tensor(act, incl9to10, eflip9red);

    //Construct extra help maps for second step. Here we need to go a step back as we need to apply a braid
    top2map1 := ((Braid(B,3,1) cat [2,1,2,1]) * ([3] cat Braid(B,2,1)) * ([3,2,1,2,1] cat Mult(B,2)) * ([3] cat Braid(B,1,2) cat [2]) * (Braid(B,1,3) cat [2,1,2,1,2]))`stdmor; 
    top2map2 := proj10to4 * Tensor(act, e4red, top2map1) * Tensor(act, incl4to10, BSId(B,2)`stdmor);
    top2map3 := Tensor(act, e10red, eflip8red) * Tensor(act, top2map2, eflip8red) * Tensor(act, e10red, inclflip8to9);

    bot2map1 := ((Braid(B,3,1) cat [2,1,2,1,2]) * ([3] cat Braid(B,2,1) cat [2]) * ([3,2,1,2,1] cat Comult(B,2)) * ([3] cat Braid(B,1,2)) * (Braid(B,1,3) cat [2,1,2,1]))`stdmor; 
    bot2map2 := Tensor(act, proj10to4, BSId(B,2)`stdmor) * Tensor(act, e4red, bot2map1) * incl4to10;
    bot2map3 := Tensor(act, e10red, projflip9to8) * Tensor(act, bot2map2, eflip8red) * Tensor(act, e10red, eflip8red);

    t2 := top2map3 * t1;
    b2 := b1 * bot2map3;

    //No braid needed; we are now at : 1212132121 \otimes 12312121	
    top3map1 := proj10to9 * Tensor(act, e9red, Mult(B,1)`stdmor) * Tensor(act, incl9to10, BSId(B,1)`stdmor);
    top3map2 := Tensor(act, e10red, eflip7red) * Tensor(act, top3map1, eflip7red) * Tensor(act, e10red, inclflip7to8);

    bot3map1 := Tensor(act, proj10to9, BSId(B,1)`stdmor) * Tensor(act, e9red, Comult(B,1)`stdmor) * incl9to10;
    bot3map2 := Tensor(act, e10red, projflip8to7) * Tensor(act, bot3map1, eflip7red) * Tensor(act, e10red, eflip7red);

    t3 := top3map2 * t2;
    b3 := b2 * bot3map2;

    //Other braiding step for 1212132121 \otimes 2312121
    top4map1 := ((Braid(B,3,1) cat [2,1,2,1]) * ([3] cat Braid(B,2,1)) * ([3,2,1,2,1] cat Mult(B,2)) * ([3] cat Braid(B,1,2) cat [2]) * (Braid(B,1,3) cat [2,1,2,1,2]))`stdmor; 
    top4map2 := proj10to4 * Tensor(act, e4red, top2map1) * Tensor(act, incl4to10, BSId(B,2)`stdmor);
    top4map3 := Tensor(act, e10red, eflip6red) * Tensor(act, top2map2, eflip6red) * Tensor(act, e10red, inclflip6to7);

    bot4map1 := ((Braid(B,3,1) cat [2,1,2,1,2]) * ([3] cat Braid(B,2,1) cat [2]) * ([3,2,1,2,1] cat Comult(B,2)) * ([3] cat Braid(B,1,2)) * (Braid(B,1,3) cat [2,1,2,1]))`stdmor; 
    bot4map2 := Tensor(act, proj10to4, BSId(B,2)`stdmor) * Tensor(act, e4red, bot2map1) * incl4to10;
    bot4map3 := Tensor(act, e10red, projflip7to6) * Tensor(act, bot2map2, eflip6red) * Tensor(act, e10red, eflip6red);

    t4 := top4map3 * t3;
    b4 := b3 * bot4map3;

    //For next reduction need one more braid on right side for (1,3): 1212132121 \otimes 312121
    top5map1 := proj10to9 * Tensor(act, e9red, Mult(B,1)`stdmor) * Tensor(act, incl9to10, BSId(B,1)`stdmor);
    top5map2 := Tensor(act, e10red, Tensor(act, BSId(B,3)`stdmor, eflip4red)) * Tensor(act, top5map1, Tensor(act, BSId(B,3)`stdmor, eflip4red)) * Tensor(act, e10red, Tensor(act, Braid(B,3,1)`stdmor, eflip4red)) * Tensor(act, e10red, inclflip4to6);

    bot5map1 := Tensor(act, proj10to9, BSId(B,1)`stdmor) * Tensor(act, e9red, Comult(B,1)`stdmor) * incl9to10;
    bot5map2 := Tensor(act, e10red, projflip6to4) * Tensor(act, e10red, Tensor(act, Braid(B,1,3)`stdmor, eflip4red)) * Tensor(act, bot5map1, Tensor(act, BSId(B,3)`stdmor, eflip4red)) * Tensor(act, e10red, Tensor(act, BSId(B,3)`stdmor, eflip4red));

    t5 := top5map2 * t4;
    b5 := b4 * bot5map2;

    //now we go from 10x5 to 11x4:
    top6map :=  Tensor(act, proj11to10, eflip4red);
    bot6map :=  Tensor(act, incl10to11, eflip4red); 

    t6 := top6map * t5;
    b6 := b5 * bot6map;

    //now we go from 11x4 to 12x3:
    top7map :=  Tensor(act, proj12to11, eflip3red) * Tensor(act, e11red, inclflip3to4); 
    bot7map :=  Tensor(act, e11red, projflip4to3) * Tensor(act, incl11to12, eflip3red); 

    t7 := top7map * t6;
    b7 := b6 * bot7map;

    //now we go from 12x3 to 13x2:
    top8map :=  Tensor(act, proj13to12, eflip2) * Tensor(act, e12red, inclflip1to3); 
    bot8map :=  Tensor(act, e12red, projflip3to1) * Tensor(act, incl12to13, eflip2); 

    t8 := top8map * t7;
    b8 := b7 * bot8map;

    //now we go from 13x2 to 14x1:
    top9map :=  Tensor(act, proj14to13, eflip1) * Tensor(act, e13red, inclflip1to2); 
    bot9map :=  Tensor(act, e13red, projflip2to1) * Tensor(act, incl13to14, eflip1); 

    t9 := top9map * t8;
    b9 := b8 * bot9map;

    //Final Step. Apply braidings and Use Mult:
    braid14 := (([2,1,2,1,3,2,1,2,3] cat Braid(B,2,1)) * ([2,1,2,1,3,2,1] cat Braid(B,3,2) cat [1,2,1,2]) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2,3,1,2,1,2]) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2] cat Braid(B,1,3) cat [2,1,2]) * (Braid(B,1,2) cat [3,2,1,2,1,3,2,1,2]))`stdmor;
    braid14back := ((Braid(B,2,1) cat [3,2,1,2,1,3,2,1,2]) * ([2,1,2,1] cat Braid(B,3,2) cat [1,2] cat Braid(B,3,1) cat [2,1,2]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2,3,1,2,1,2]) * ([2,1,2,1,3,2,1] cat Braid(B,2,3) cat [1,2,1,2]) * ([2,1,2,1,3,2,1,2,3] cat Braid(B,1,2)))`stdmor;

    top10map := proj14to1 * braid14back * Tensor(act, BSId(B,[2,1,2,1,3,2,1,2,3,1,2,1,2])`stdmor, Mult(B,1)`stdmor) * Tensor(act, braid14, eflip1) * Tensor(act, incl1to14, eflip1);
    bot10map := Tensor(act, proj14to1, eflip1) * Tensor(act, braid14back, eflip1) * Tensor(act, BSId(B,[2,1,2,1,3,2,1,2,3,1,2,1,2])`stdmor, Comult(B,1)`stdmor) * braid14 * incl1to14;

    t10:= top10map * t9;
    b10 := b9 * bot10map;

    //Now the trace:

    trace10 := t10 * middle * b10;

    //We need to compate this to a partial trace around 14:
    partial13 :=  Tensor(act, e13red, Cap(B,2)`stdmor) * Tensor(act, incl13to14, BSId(B,2)`stdmor) * Tensor(act, e14red, root^6*(BSId(B,2)`stdmor)) *  Tensor(act, proj14to13, BSId(B,2)`stdmor) * Tensor(act, e13red, Cup(B,2)`stdmor);

    partial12 :=  Tensor(act, e12red, Cap(B,1)`stdmor) * Tensor(act, incl12to13, BSId(B,1)`stdmor) * Tensor(act, partial13, BSId(B,1)`stdmor) *  Tensor(act, proj13to12, BSId(B,1)`stdmor) * Tensor(act, e12red, Cup(B,1)`stdmor);

    partial11 :=  Tensor(act, e11red, Cap(B,2)`stdmor) * Tensor(act, incl11to12, BSId(B,2)`stdmor) * Tensor(act, partial12, BSId(B,2)`stdmor) *  Tensor(act, proj12to11, BSId(B,2)`stdmor) * Tensor(act, e11red, Cup(B,2)`stdmor);

    partial10 :=  Tensor(act, e10red, Cap(B,3)`stdmor) * Tensor(act, incl10to11, BSId(B,3)`stdmor) * Tensor(act, partial11, BSId(B,3)`stdmor) *  Tensor(act, proj11to10, BSId(B,3)`stdmor) * Tensor(act, e10red, Cup(B,3)`stdmor);

    //This then gives a second middle term where we can compute the trace:

    middle14 := Tensor(act, partial10, eflip10red);
    trace14 := t10 * middle14 * b10;

    d10 := trace10`mat[1,1] / trace14`mat[1,1];
    d14 := trace14`mat[1,1] / trace14`mat[1,1];

    T2 := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("All assertions correct. The dimension of ew is %o. The dimension of ed is %o. Total time for the calculation took %o, used space was %o.", d10, d14, T2, S);
end procedure;

//for completion sake we include the cell of a-value 1 in H3. The representatives d=1, w=d21, are the same as in the dihedral case
procedure H3_a1_complete()
    //We run all tests step by step and return the total time and space needed:
    ResetMaximumMemoryUsage();
    T := Time();

    //AttachSpec("ASLoc.spec");
    carH3 := CartanMatrix("H3");
    W := CoxeterGroup(GrpFPCox, "H3");

    //The cartan matrix lives over a cyclotomic field including phi
    f := BaseRing(carH3);
    FR := RationalFunctionField(f,Rank(W));

    //We can construct the right BSCategory with the new field
    B := New(BSCat);
    B`C := carH3;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    FA := B`FAct;

    act := function(w)
        return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;

    //Now we create idempotents
    //ei will be the idempotent of the word of length i
    e1 := BSId(B,1)`stdmor;
    e2 := Tensor(act, e1, [id,t]);

    //For e3 one need a sum of two terms; 
    //We use the shorthand fi_s for the tensor product of ei with s
    //We then define up and down maps from fi_s to e(i-1)
    //the coefficient k1_3 is then computed as in the paper
    f2_s := Tensor(act, e2, [id,s]);
    d2_1 := e1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * f2_s;
    u2_1 := f2_s * LocalisedLLUp(B,[1,2,1],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := b1_3`mat[1,1] / e1`mat[1,1];
    e3 := f2_s - 1/k1_3 * u2_1 * d2_1;

    assert e3 eq e3 * e3;
    
    //Now we check the positive root:
    //The positive root should be (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3; Check:    
    root := (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3;
    assert Matrix(Mult(B,1)`stdmor * Tensor(act, BSId(B,1)`stdmor, root*BSId(B,1)`stdmor) * Comult(B,1)`stdmor) eq Matrix(BSId(B,1)`stdmor);
    assert Matrix(Mult(B,2)`stdmor * Tensor(act, BSId(B,2)`stdmor, root*BSId(B,2)`stdmor) * Comult(B,2)`stdmor) eq Matrix(BSId(B,2)`stdmor);
    assert Matrix(Mult(B,3)`stdmor * Tensor(act, BSId(B,3)`stdmor, root*BSId(B,3)`stdmor) * Comult(B,3)`stdmor) eq Matrix(BSId(B,3)`stdmor);
    
    //Finally we compute the partial trace and dimension:
    //We create partial trace map around e3 to go to e1 
    dtop121 := LocalisedLLDown(B,[1,2,1,1,2],[1,1,1,1,1]);
    dbot121 := LocalisedLLUp(B,[1,2,1,1,2],[1,1,1,1,1]);
    partial_trace1 := dtop121 * (Tensor(act,e3,root*e2)) * dbot121; 

    //The dimension is then partial_1(partial_trace)
    trace_morphism := Mult(B,1)`stdmor * (Tensor(act, partial_trace1, e1)) * Comult(B,1)`stdmor;
    dim := Matrix(trace_morphism)[1,1] / Matrix(e1)[1,1];
    
    assert dim eq f.1;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("All assertions correct. The dimension of ew is %o. Total time for the calculation took %o, used space was %o.", dim, T, S);
end procedure;


//Now the middle cell in H4. Here we have 3 cases. We only calculate the dimensions of the smallest 2 or 3 elements. This is enough for our statement
procedure H4_middle_1()
    ResetMaximumMemoryUsage();
    T := Time();

    AttachSpec("ASLoc.spec");
    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");

    f := BaseRing(carH4);
    FR := RationalFunctionField(f,Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();
    FA := B`FAct;
    act := function(w)
        return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;
    v := W.4;

    //Create idempotents:
    //d:=232432; w1=d1234; (w2=(w1)1234) w2 is actually not needed
    //We number the words as the plethysm graph does not branch out, i.e. e5 stands for (23243), the first 5 letters of d

    e1 := BSId(B,2)`stdmor;

    e2 := Tensor(act,e1,[id,u]);

    //e2 x 2 = e3 + e1
    f2_t := Tensor(act, e2, [id,t]);
    d2_1 := e1 * LocalisedLLDown(B,[2,3,2],[1,0,0]) * f2_t;
    u2_1 := f2_t * LocalisedLLUp(B,[2,3,2],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := Matrix(b1_3)[1,1] / Matrix(e1)[1,1];
    //k1_3 := -1;
    e3 := f2_t - 1/k1_3 * u2_1 * d2_1;
    proj3to1, incl1to3 := DecomposeIdem(e3);
    e3red := proj3to1 * e3 * incl1to3;

    e4 := Tensor(act,e3red,[id,v]);
    proj4to3, incl3to4 := DecomposeIdem(e4);
    e4red := proj4to3 * e4 * incl3to4;
    incl1to4 := Tensor(act, incl1to3, [id,v]) * incl3to4;
    proj4to1 := proj4to3 * Tensor(act, proj3to1, [id,v]);

    //e4 x 3 = e5 + e3 with Braiding
    f4_u := Tensor(act, e4red, [id,u]);
    d4_3 := e3red * proj3to1 * Braid(B,3,2)`stdmor * LocalisedLLDown(B,[2,3,2,4,3],[1,1,1,0,0]) * Tensor(act, incl1to4, BSId(B,3)`stdmor) * f4_u;
    u4_3 := f4_u * Tensor(act, proj4to1, BSId(B,3)`stdmor) * LocalisedLLUp(B,[2,3,2,4,3],[1,1,1,0,0]) * Braid(B,2,3)`stdmor * incl1to3 * e3red;
    b3_5 := d4_3 * u4_3;
    k3_5 := Matrix(b3_5)[1,1];
    //k3_5 := -1;
    e5 := f4_u - 1/k3_5 * u4_3 * d4_3;
    proj5to4, incl4to5 := DecomposeIdem(e5);
    e5red := proj5to4 * e5 * incl4to5;
    incl1to5 := Tensor(act, incl1to4, [id,u]) * incl4to5;
    proj5to1 := proj5to4 * Tensor(act, proj4to1, [id,u]);

    //e5 x 2 = e6 + e4 with Braiding
    f5_t := Tensor(act, e5red, [id,t]);
    d5_4 := e4red * proj4to1 * Tensor(act, BSId(B,[2,3])`stdmor, Braid(B,4,2)`stdmor) * LocalisedLLDown(B,[2,3,2,4,3,2],[1,1,1,1,0,0]) * Tensor(act, incl1to5, BSId(B,2)`stdmor) * f5_t;
    u5_4 := f5_t * Tensor(act, proj5to1, BSId(B,2)`stdmor) * LocalisedLLUp(B,[2,3,2,4,3,2],[1,1,1,1,0,0]) * Tensor(act, BSId(B,[2,3])`stdmor, Braid(B,2,4)`stdmor) * incl1to4 * e4red;
    b4_6 := d5_4 * u5_4;
    k4_6 := Matrix(b4_6)[1,1];
    //k4_6 := -1;
    e6 := f5_t - 1/k4_6 * u5_4 * d5_4;
    proj6to5, incl5to6 := DecomposeIdem(e6);
    e6red := proj6to5 * e6 * incl5to6;
    incl1to6 := Tensor(act, incl1to5, [id,t]) * incl5to6;
    proj6to1 := proj6to5 * Tensor(act, proj5to1, [id,t]);

    e7 := Tensor(act,e6red,[id,s]);
    proj7to6, incl6to7 := DecomposeIdem(e7);
    e7red := proj7to6 * e7 * incl6to7;
    incl5to7 := Tensor(act, incl5to6, [id,s]) * incl6to7;
    proj7to5 := proj7to6 * Tensor(act, proj6to5, [id,s]);
    incl1to7 := Tensor(act, incl1to6, [id,s]) * incl6to7;
    proj7to1 := proj7to6 * Tensor(act, proj6to1, [id,s]);

    //e7 x 2 = e8 + e6
    f7_t := Tensor(act, e7red, [id,t]);
    d7_6 := proj6to5 * Tensor(act, e5red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl5to7, BSId(B,2)`stdmor) * f7_t;
    u7_6 := f7_t * Tensor(act, proj7to5, BSId(B,2)`stdmor)  * Tensor(act, e5red, LocalisedLLUp(B,[2,1,2],[1,0,0]))  * incl5to6;
    b6_8 := d7_6 * u7_6;
    k6_8 := Matrix(b6_8)[1,1];
    //k6_8 := -f.1;
    e8 := f7_t - 1/k6_8 * u7_6 * d7_6;
    proj8to7, incl7to8 := DecomposeIdem(e8);
    e8red := proj8to7 * e8 * incl7to8;
    incl1to8 := Tensor(act, incl1to7, [id,t]) * incl7to8;
    proj8to1 := proj8to7 * Tensor(act, proj7to1, [id,t]);

    //e8 x 3 = e9 + e7
    f8_u := Tensor(act, e8red, [id,u]);
    d8_7 := proj7to1 * Tensor(act, BSId(B,[2,3])`stdmor, Tensor(act, Braid(B,4,2)`stdmor, BSId(B,[3,2,1])`stdmor)) * Tensor(act, BSId(B,[2,3,4])`stdmor, Tensor(act, Braid(B,3,2)`stdmor, BSId(B,[1])`stdmor)) * Tensor(act, BSId(B,[2,3,4,3,2])`stdmor, Braid(B,1,3)`stdmor) * LocalisedLLDown(B,[2,3,4,3,2,1,3,2,3],[1,1,1,1,1,1,1,0,0]) * Tensor(act, BSId(B,[2,3,4,3,2])`stdmor, Tensor(act, Braid(B,3,1)`stdmor, BSId(B,[2,3])`stdmor)) * Tensor(act, BSId(B,[2,3,4])`stdmor, Tensor(act, Braid(B,2,3)`stdmor, BSId(B,[1,2,3])`stdmor)) * Tensor(act, BSId(B,[2,3])`stdmor, Tensor(act, Braid(B,2,4)`stdmor, BSId(B,[3,2,1,2,3])`stdmor)) * Tensor(act, incl1to8, BSId(B,3)`stdmor) * f8_u;
    u8_7 := f8_u * Tensor(act, proj8to1, BSId(B,3)`stdmor) * Tensor(act, BSId(B,[2,3])`stdmor, Tensor(act, Braid(B,4,2)`stdmor, BSId(B,[3,2,1,2,3])`stdmor)) * Tensor(act, BSId(B,[2,3,4])`stdmor, Tensor(act, Braid(B,3,2)`stdmor, BSId(B,[1,2,3])`stdmor)) * Tensor(act, BSId(B,[2,3,4,3,2])`stdmor, Tensor(act, Braid(B,1,3)`stdmor, BSId(B,[2,3])`stdmor)) * LocalisedLLUp(B,[2,3,4,3,2,1,3,2,3],[1,1,1,1,1,1,1,0,0]) * Tensor(act, BSId(B,[2,3,4,3,2])`stdmor, Braid(B,3,1)`stdmor) * Tensor(act, BSId(B,[2,3,4])`stdmor, Tensor(act, Braid(B,2,3)`stdmor, BSId(B,[1])`stdmor)) * Tensor(act, BSId(B,[2,3])`stdmor, Tensor(act, Braid(B,2,4)`stdmor, BSId(B,[3,2,1])`stdmor)) * incl1to7;
    b7_9 := d8_7 * u8_7;
    k7_9 := Matrix(b7_9)[1,1];
    //k7_9 := -1;
    e9 := f8_u - 1/k7_9 * u8_7 * d8_7;
    proj9to8, incl8to9 := DecomposeIdem(e9);
    e9red := proj9to8 * e9 * incl8to9;
    incl1to9 := Tensor(act, incl1to8, [id,u]) * incl8to9;
    proj9to1 := proj9to8 * Tensor(act, proj8to1, [id,u]);

    //e9 x 4 = e10 + e8; 232432123 
    br9to8 := ([3,2,4,3,2,1] cat Braid(B,4,2) cat [3,4]) * ([3,2,4,3,2] cat Braid(B,4,1) cat [2,3,4]) * ([3,2,4,3] cat Braid(B,4,2) cat [1,2,3,4]) * ([3,2] cat Braid(B,3,4) cat [2,1,2,3,4]) * (Braid(B,2,3) cat [4,3,2,1,2,3,4]);
    br8to9 := ([3,2,4,3,2,1] cat Braid(B,4,2)) * ([3,2,4,3,2] cat Braid(B,4,1) cat [2]) * ([3,2,4,3] cat Braid(B,4,2) cat [1,2]) * ([3,2] cat Braid(B,3,4) cat [2,1,2]) * (Braid(B,2,3) cat [4,3,2,1,2]);
    br9from8 := (Braid(B,3,2) cat [4,3,2,1,2,3,4]) * ([3,2] cat Braid(B,4,3) cat [2,1,2,3,4]) * ([3,2,4,3] cat Braid(B,2,4) cat [1,2,3,4]) * ([3,2,4,3,2] cat Braid(B,1,4) cat [2,3,4]) * ([3,2,4,3,2,1] cat Braid(B,2,4) cat [3,4]);
    br8from9 := (Braid(B,3,2) cat [4,3,2,1,2]) * ([3,2] cat Braid(B,4,3) cat [2,1,2]) * ([3,2,4,3] cat Braid(B,2,4) cat [1,2]) * ([3,2,4,3,2] cat Braid(B,1,4) cat [2]) * ([3,2,4,3,2,1] cat Braid(B,2,4));
    f9_v := Tensor(act, e9red, [id,v]);
    d9_8 :=  proj8to1 * br8from9`stdmor * Tensor(act, BSId(B,[3,2,4,3,2,1,2])`stdmor, LocalisedLLDown(B,[4,3,4],[1,0,0])) * br9to8`stdmor * Tensor(act, incl1to9, BSId(B,4)`stdmor) * f9_v;
    u9_8 := f9_v * Tensor(act, proj9to1, BSId(B,4)`stdmor) * br9from8`stdmor * Tensor(act, BSId(B,[3,2,4,3,2,1,2])`stdmor, LocalisedLLUp(B,[4,3,4],[1,0,0])) * br8to9`stdmor * incl1to8;
    b8_10 := d9_8 * u9_8;
    k8_10 := Matrix(b8_10)[1,1];
    //k8_10 := -1;
    e10 := f9_v - 1/k8_10 * u9_8 * d9_8;
    proj10to9, incl9to10 := DecomposeIdem(e10);
    e10red := proj10to9 * e10 * incl9to10;
    incl1to10 := Tensor(act, incl1to9, [id,v]) * incl9to10;
    proj10to1 := proj10to9 * Tensor(act, proj9to1, [id,v]);

    //e11
    e11 := Tensor(act,e10red,[id,s]);
    proj11to10, incl10to11 := DecomposeIdem(e11);
    e11red := proj11to10 * e11 * incl10to11;
    incl1to11 := Tensor(act, incl1to10, [id,s]) * incl10to11;
    proj11to1 := proj11to10 * Tensor(act, proj10to1, [id,s]);
    incl9to11 := Tensor(act, incl9to10, [id,s]) * incl10to11;
    proj11to9 := proj11to10 * Tensor(act, proj10to9, [id,s]);

    //e12: 23243212341 x 2 
    br11to10 := ([2,3,4,3,2,1,2,3] cat Braid(B,2,4) cat [1,2]) * ([2,3,4,3,2,1] cat Braid(B,3,2) cat [4,1,2]) * ([2,3,4,3,2] cat Braid(B,3,1) cat [2,3,4,1,2]) * ([2,3,4] cat Braid(B,2,3) cat [1,2,3,4,1,2]) * ([2,3] cat Braid(B,2,4) cat [3,2,1,2,3,4,1,2]);
    br10to11 := ([2,3,4,3,2,1,2,3] cat Braid(B,2,4)) * ([2,3,4,3,2,1] cat Braid(B,3,2) cat [4]) * ([2,3,4,3,2] cat Braid(B,3,1) cat [2,3,4]) * ([2,3,4] cat Braid(B,2,3) cat [1,2,3,4]) * ([2,3] cat Braid(B,2,4) cat [3,2,1,2,3,4]);
    br11from10 := ([2,3] cat Braid(B,4,2) cat [3,2,1,2,3,4,1,2]) * ([2,3,4] cat Braid(B,3,2) cat [1,2,3,4,1,2]) * ([2,3,4,3,2] cat Braid(B,1,3) cat [2,3,4,1,2]) * ([2,3,4,3,2,1] cat Braid(B,2,3) cat [4,1,2]) * ([2,3,4,3,2,1,2,3] cat Braid(B,4,2) cat [1,2]); 
    br10from11 := ([2,3] cat Braid(B,4,2) cat [3,2,1,2,3,4]) * ([2,3,4] cat Braid(B,3,2) cat [1,2,3,4]) * ([2,3,4,3,2] cat Braid(B,1,3) cat [2,3,4]) * ([2,3,4,3,2,1] cat Braid(B,2,3) cat [4]) * ([2,3,4,3,2,1,2,3] cat Braid(B,4,2)); 
    f11_t := Tensor(act, e11red, [id,t]);
    d11_10 :=  proj10to1 * br10from11`stdmor * Tensor(act, BSId(B,[2,3,4,3,2,1,2,3,4])`stdmor, LocalisedLLDown(B,[2,1,2],[1,0,0])) * br11to10`stdmor * Tensor(act, incl1to11, BSId(B,2)`stdmor) * f11_t;
    u11_10 := f11_t * Tensor(act, proj11to1, BSId(B,2)`stdmor) * br11from10`stdmor * Tensor(act, BSId(B,[2,3,4,3,2,1,2,3,4])`stdmor, LocalisedLLUp(B,[2,1,2],[1,0,0])) * br10to11`stdmor * incl1to10;
    b10_12 := d11_10 * u11_10;
    k10_12 := Matrix(b10_12)[1,1];
    //k10_12 := -f.1;
    e12 := f11_t - 1/k10_12 * u11_10 * d11_10;
    proj12to11, incl11to12 := DecomposeIdem(e12);
    e12red := proj12to11 * e12 * incl11to12;
    incl1to12 := Tensor(act, incl1to11, [id,t]) * incl11to12;
    proj12to1 := proj12to11 * Tensor(act, proj11to1, [id,t]);
    incl9to12 := Tensor(act, incl9to11, [id,t]) * incl11to12;
    proj12to9 := proj12to11 * Tensor(act, proj11to9, [id,t]);

    //e13 232432123412 3
    br12to11 := ([3,2,4,3,2,1,2,3,4] cat Braid(B,3,1) cat [2,3]) * ([3,2,4,3,2,1,2] cat Braid(B,4,3) cat [1,2,3]) * ([3,2,4,3,2,1] cat Braid(B,4,2) cat [3,4,1,2,3]) * ([3,2,4,3,2] cat Braid(B,4,1) cat [2,3,4,1,2,3]) * ([3,2,4,3] cat Braid(B,4,2) cat [1,2,3,4,1,2,3]) * ([3,2] cat Braid(B,3,4) cat [2,1,2,3,4,1,2,3]) * (Braid(B,2,3) cat [4,3,2,1,2,3,4,1,2,3]);
    br11to12 := ([3,2,4,3,2,1,2,3,4] cat Braid(B,3,1)) * ([3,2,4,3,2,1,2] cat Braid(B,4,3) cat [1]) * ([3,2,4,3,2,1] cat Braid(B,4,2) cat [3,4,1]) * ([3,2,4,3,2] cat Braid(B,4,1) cat [2,3,4,1]) * ([3,2,4,3] cat Braid(B,4,2) cat [1,2,3,4,1]) * ([3,2] cat Braid(B,3,4) cat [2,1,2,3,4,1]) * (Braid(B,2,3) cat [4,3,2,1,2,3,4,1]);
    br12from11 := (Braid(B,3,2) cat [4,3,2,1,2,3,4,1,2,3]) * ([3,2] cat Braid(B,4,3) cat [2,1,2,3,4,1,2,3]) * ([3,2,4,3] cat Braid(B,2,4) cat [1,2,3,4,1,2,3]) * ([3,2,4,3,2] cat Braid(B,1,4) cat [2,3,4,1,2,3]) * ([3,2,4,3,2,1] cat Braid(B,2,4) cat [3,4,1,2,3]) * ([3,2,4,3,2,1,2] cat Braid(B,3,4) cat [1,2,3]) * ([3,2,4,3,2,1,2,3,4] cat Braid(B,1,3
    ) cat [2,3]);
    br11from12 := (Braid(B,3,2) cat [4,3,2,1,2,3,4,1]) * ([3,2] cat Braid(B,4,3) cat [2,1,2,3,4,1]) * ([3,2,4,3] cat Braid(B,2,4) cat [1,2,3,4,1]) * ([3,2,4,3,2] cat Braid(B,1,4) cat [2,3,4,1]) * ([3,2,4,3,2,1] cat Braid(B,2,4) cat [3,4,1]) * ([3,2,4,3,2,1,2] cat Braid(B,3,4) cat [1]) * ([3,2,4,3,2,1,2,3,4] cat Braid(B,1,3));
    f12_u := Tensor(act, e12red, [id,u]);
    d12_11 :=  proj11to1 * br11from12`stdmor * Tensor(act, BSId(B,[3,2,4,3,2,1,2,3,4,1])`stdmor, LocalisedLLDown(B,[3,2,3],[1,0,0])) * br12to11`stdmor * Tensor(act, incl1to12, BSId(B,3)`stdmor) * f12_u;
    u12_11 := f12_u * Tensor(act, proj12to1, BSId(B,3)`stdmor) * br12from11`stdmor * Tensor(act, BSId(B,[3,2,4,3,2,1,2,3,4,1])`stdmor, LocalisedLLUp(B,[3,2,3],[1,0,0])) * br11to12`stdmor * incl1to11;
    b11_13 := d12_11 * u12_11;
    k11_13 := Matrix(b11_13)[1,1];
    //k11_13 := -f.1;
    e13 := f12_u - 1/k11_13 * u12_11 * d12_11;
    proj13to12, incl12to13 := DecomposeIdem(e13);
    e13red := proj13to12 * e13 * incl12to13;
    incl1to13 := Tensor(act, incl1to12, [id,u]) * incl12to13;
    proj13to1 := proj13to12 * Tensor(act, proj12to1, [id,u]);
    incl9to13 := Tensor(act, incl9to12, [id,u]) * incl12to13;
    proj13to9 := proj13to12 * Tensor(act, proj12to9, [id,u]);

    //e14=2324321234123: e13 x 4 = e14 + e12 + e6
    br13to12 := ([1] cat Braid(B,4,2) cat [3,4]) * (Braid(B,4,1) cat [2,3,4]);
    br12to13 := ([1] cat Braid(B,4,2)) * (Braid(B,4,1) cat [2]);
    br13from12 := (Braid(B,1,4) cat [2,3,4]) * ([1] cat Braid(B,2,4) cat [3,4]);
    br12from13 := (Braid(B,1,4) cat [2]) * ([1] cat Braid(B,2,4));
    f13_v := Tensor(act, e13red, [id,v]);
    d13_12 :=  proj12to9 * Tensor(act, e9red,br12from13`stdmor) * Tensor(act, Tensor(act, e9red, BSId(B,[1,2])`stdmor), LocalisedLLDown(B,[4,3,4],[1,0,0])) * Tensor(act, e9red, br13to12`stdmor) * Tensor(act, incl9to13, BSId(B,4)`stdmor) * f13_v;
    u13_12 := f13_v * Tensor(act, proj13to9, BSId(B,4)`stdmor) * Tensor(act, e9red,br13from12`stdmor) * Tensor(act, Tensor(act, e9red,BSId(B,[1,2])`stdmor), LocalisedLLUp(B,[4,3,4],[1,0,0])) * Tensor(act, e9red,br12to13`stdmor) * incl9to12;
    b12_14 := d13_12 * u13_12;
    k12_14 := Matrix(b12_14)[1,1];
    //k12_14 := -1;
    br13to6 := (Braid(B,3,2) cat [4,3,2]) * ([3,2] cat Braid(B,4,3) cat [2]) * ([3] cat Braid(B,4,2) cat [3] cat Braid(B,2,4)) * ([3,4] cat Braid(B,3,2) cat [4]) * (Braid(B,4,3) cat [2,3,4]) * ([4,3] cat Braid(B,2,4) cat [3,4]);
    br6to13 := ([4,3] cat Braid(B,4,2) cat [3,4]) * (Braid(B,3,4) cat [2,3,4]) * ([3,4] cat Braid(B,2,3) cat [4]) * ([3] cat Braid(B,2,4) cat [3] cat Braid(B,4,2)) * ([3,2] cat Braid(B,3,4) cat [2]) * (Braid(B,2,3) cat [4,3,2]);

    d13_6 :=  proj6to1 * br13to6`stdmor * LocalisedLLDown(B,[2,3,2,4,3,2,1,2,3,4,1,2,3,4],[0,1,0,1,1,1,1,0,1,1,1,0,0,0]) * Tensor(act, incl1to13, BSId(B,4)`stdmor) * f13_v;
    u13_6 :=  f13_v * Tensor(act, proj13to1, BSId(B,4)`stdmor) * LocalisedLLUp(B,[2,3,2,4,3,2,1,2,3,4,1,2,3,4],[0,1,0,1,1,1,1,0,1,1,1,0,0,0]) * br6to13`stdmor * incl1to6;
    b6_14 := d13_6 * u13_6;
    k6_14 := Matrix(b6_14)[1,1];
    //k6_14 := 
    e14 := f13_v - 1/k12_14 * u13_12 * d13_12 - 1/k6_14 * u13_6 * d13_6;
    proj14to13, incl13to14 := DecomposeIdem(e14);
    e14red := proj14to13 * e14 * incl13to14;
    incl1to14 := Tensor(act, incl1to13, [id,v]) * incl13to14;
    proj14to1 := proj14to13 * Tensor(act, proj13to1, [id,v]);

    //Now Dimension of ed
    //This is still small enough that one can still use LightLeaves

    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;

    //Computing the next three lines not in one line should make it faster, as we try to reduce the matrix sizes.
    //We need this extra braid because of the result of LightLeave
    d_top := proj6to1 * ([2,3] cat Braid(B,4,2) cat [3,2])`stdmor * LocalisedLLDown(B,[2,3,2,4,3,2,2,3,2,4,3,2],[1,1,1,1,1,1,0,0,0,0,0,0]) * Tensor(act, incl1to6, incl1to6);
    d_bot := Tensor(act, proj6to1, proj6to1) * LocalisedLLUp(B,[2,3,2,4,3,2,2,3,2,4,3,2],[1,1,1,1,1,1,0,0,0,0,0,0]) * ([2,3] cat Braid(B,2,4) cat [3,2])`stdmor * incl1to6;

    trace_d := d_top * Tensor(act, e6red, root^6*e6red) * d_bot;
    //The result is 720. Therefore need to scale other traces by that amount.

    dim_d := trace_d`mat[1,1]/trace_d`mat[1,1];
    Sprintf("The dimension of d=232432 is %o", dim_d);

    //e10 = ew1
    partial9 :=  Tensor(act, e9red, Cap(B,4)`stdmor) * Tensor(act, incl9to10, BSId(B,4)`stdmor) * Tensor(act, e10red, root^6*(BSId(B,4)`stdmor)) *  Tensor(act, proj10to9, BSId(B,4)`stdmor) * Tensor(act, e9red, Cup(B,4)`stdmor);

    partial8 :=  Tensor(act, e8red, Cap(B,3)`stdmor) * Tensor(act, incl8to9, BSId(B,3)`stdmor) * Tensor(act, partial9, BSId(B,3)`stdmor) *  Tensor(act, proj9to8, BSId(B,3)`stdmor) * Tensor(act, e8red, Cup(B,3)`stdmor);

    partial7 :=  Tensor(act, e7red, Cap(B,2)`stdmor) * Tensor(act, incl7to8, BSId(B,2)`stdmor) * Tensor(act, partial8, BSId(B,2)`stdmor) *  Tensor(act, proj8to7, BSId(B,2)`stdmor) * Tensor(act, e7red, Cup(B,2)`stdmor);

    partial6 :=  Tensor(act, e6red, Cap(B,1)`stdmor) * Tensor(act, incl6to7, BSId(B,1)`stdmor) * Tensor(act, partial7, BSId(B,1)`stdmor) *  Tensor(act, proj7to6, BSId(B,1)`stdmor) * Tensor(act, e6red, Cup(B,1)`stdmor);

    trace_w1 := d_top * Tensor(act, partial6, e6red) * d_bot;
    dim_w1 := trace_w1`mat[1,1]/trace_d`mat[1,1];
    Sprintf("The dimension of w1=2324321234 is %o", dim_w1);
    //Result is 2*f.1

    //e14 = ew2
    partial13 :=  Tensor(act, e13red, Cap(B,4)`stdmor) * Tensor(act, incl13to14, BSId(B,4)`stdmor) * Tensor(act, e14red, root^6*(BSId(B,4)`stdmor)) *  Tensor(act, proj14to13, BSId(B,4)`stdmor) * Tensor(act, e13red, Cup(B,4)`stdmor);

    partial12 :=  Tensor(act, e12red, Cap(B,3)`stdmor) * Tensor(act, incl12to13, BSId(B,3)`stdmor) * Tensor(act, partial13, BSId(B,3)`stdmor) *  Tensor(act, proj13to12, BSId(B,3)`stdmor) * Tensor(act, e12red, Cup(B,3)`stdmor);

    partial11 :=  Tensor(act, e11red, Cap(B,2)`stdmor) * Tensor(act, incl11to12, BSId(B,2)`stdmor) * Tensor(act, partial12, BSId(B,2)`stdmor) *  Tensor(act, proj12to11, BSId(B,2)`stdmor) * Tensor(act, e11red, Cup(B,2)`stdmor);

    partial10 :=  Tensor(act, e10red, Cap(B,1)`stdmor) * Tensor(act, incl10to11, BSId(B,1)`stdmor) * Tensor(act, partial11, BSId(B,1)`stdmor) *  Tensor(act, proj11to10, BSId(B,1)`stdmor) * Tensor(act, e10red, Cup(B,1)`stdmor);

    partial9 :=  Tensor(act, e9red, Cap(B,4)`stdmor) * Tensor(act, incl9to10, BSId(B,4)`stdmor) * Tensor(act, partial10, BSId(B,4)`stdmor) *  Tensor(act, proj10to9, BSId(B,4)`stdmor) * Tensor(act, e9red, Cup(B,4)`stdmor);

    partial8 :=  Tensor(act, e8red, Cap(B,3)`stdmor) * Tensor(act, incl8to9, BSId(B,3)`stdmor) * Tensor(act, partial9, BSId(B,3)`stdmor) *  Tensor(act, proj9to8, BSId(B,3)`stdmor) * Tensor(act, e8red, Cup(B,3)`stdmor);

    partial7 :=  Tensor(act, e7red, Cap(B,2)`stdmor) * Tensor(act, incl7to8, BSId(B,2)`stdmor) * Tensor(act, partial8, BSId(B,2)`stdmor) *  Tensor(act, proj8to7, BSId(B,2)`stdmor) * Tensor(act, e7red, Cup(B,2)`stdmor);

    partial6 :=  Tensor(act, e6red, Cap(B,1)`stdmor) * Tensor(act, incl6to7, BSId(B,1)`stdmor) * Tensor(act, partial7, BSId(B,1)`stdmor) *  Tensor(act, proj7to6, BSId(B,1)`stdmor) * Tensor(act, e6red, Cup(B,1)`stdmor);

    trace_w2 := d_top * Tensor(act, partial6, e6red) * d_bot;
    dim_w2 := trace_w2`mat[1,1]/trace_d`mat[1,1];
    Sprintf("The dimension of w2 is %o", dim_w2);
    //The result is 4*f.1+3;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("The total time for the calculation took %o, used space was %o.", T, S);
end procedure;

procedure H4_middle_9()
    ResetMaximumMemoryUsage();
    T := Time();

    AttachSpec("ASLoc.spec");
    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");

    f := BaseRing(carH4);
    FR := RationalFunctionField(f,Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();
    FA := B`FAct;
    act := function(w)
        return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;
    v := W.4;

    //Create idempotents:

    //Word is d=121214, w1:= 121214342121
    //Label the elements again from 1 to 12

    e1 := BSId(B,1)`stdmor;

    e2 := Tensor(act,e1,[id,t]);

    //e2 x 1 = e3 + e1
    f2_s := Tensor(act, e2, [id,s]);
    d2_1 := e1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * f2_s;
    u2_1 := f2_s * LocalisedLLUp(B,[1,2,1],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := Matrix(b1_3)[1,1]/Matrix(e1)[1,1];
    //k1_3 := -f.1;
    e3 := f2_s - 1/k1_3 * u2_1 * d2_1;

    //e3 x 2 = e4 + e2
    f3_t := Tensor(act, e3, [id,t]);
    d3_2 := e2 * LocalisedLLDown(B,[1,2,1,2],[1,1,0,0]) * f3_t;
    u3_2 := f3_t * LocalisedLLUp(B,[1,2,1,2],[1,1,0,0]) * e2;
    b2_4 := d3_2 * u3_2;
    k2_4 := Matrix(b2_4)[1,1]/Matrix(e2)[1,1];
    //k2_4 := -1;
    e4 := f3_t - 1/k2_4 * u3_2 * d3_2;
    proj4to1, incl1to4 := DecomposeIdem(e4);
    e4red := proj4to1 * e4 * incl1to4;

    //e4 x 1 = e5 + e3
    f4_s := Tensor(act, e4red, [id,s]);
    d4_3 := e3 * LocalisedLLDown(B,[1,2,1,2,1],[1,1,1,0,0]) * Tensor(act, incl1to4, BSId(B,1)`stdmor) * f4_s;
    u4_3 := f4_s * Tensor(act, proj4to1, BSId(B,1)`stdmor) * LocalisedLLUp(B,[1,2,1,2,1],[1,1,1,0,0]) * e3;
    b3_5 := d4_3 * u4_3;
    k3_5 := Matrix(b3_5)[1,1]/Matrix(e3)[1,1];
    //k3_5 := -f.1+1;
    e5 := f4_s - 1/k3_5 * u4_3 * d4_3;
    proj5to4, incl4to5 := DecomposeIdem(e5);
    e5red := proj5to4 * e5 * incl4to5;
    incl1to5 := Tensor(act, incl1to4, [id,s]) * incl4to5;
    proj5to1 := proj5to4 * Tensor(act, proj4to1, [id,s]);

    e6 := Tensor(act,e5red,BSId(B,4)`stdmor);
    proj6to5, incl5to6 := DecomposeIdem(e6);
    e6red := proj6to5 * e6 * incl5to6;
    incl4to6 := Tensor(act, incl4to5, [id,v]) * incl5to6;
    proj6to4 := proj6to5 * Tensor(act, proj5to4, [id,v]);
    incl1to6 := Tensor(act, incl1to5, [id,v]) * incl5to6;
    proj6to1 := proj6to5 * Tensor(act, proj5to1, [id,v]);

    e7 := Tensor(act,e6red,BSId(B,3)`stdmor);
    proj7to6, incl6to7 := DecomposeIdem(e7);
    e7red := proj7to6 * e7 * incl6to7;
    incl4to7 := Tensor(act, incl4to6, [id,u]) * incl6to7;
    proj7to4 := proj7to6 * Tensor(act, proj6to4, [id,u]);
    incl1to7 := Tensor(act, incl1to6, [id,u]) * incl6to7;
    proj7to1 := proj7to6 * Tensor(act, proj6to1, [id,u]);

    //e7 x 4 = e8 + ed
    f7_v := Tensor(act, e7red, [id,v]);
    d7_d := e6red * proj6to4 * Tensor(act, e4red, LocalisedLLDown(B,[1,4,3,4],[1,1,0,0])) * Tensor(act, incl4to7, BSId(B,[4])`stdmor) * f7_v;
    u7_d := f7_v * Tensor(act, proj7to4, BSId(B,[4])`stdmor) * Tensor(act, e4red, LocalisedLLUp(B,[1,4,3,4],[1,1,0,0])) * incl4to6 * e6red;
    bd_8 := d7_d * u7_d;
    kd_8 := Matrix(bd_8)[1,1]/Matrix(e6red)[1,1];
    //kd_8 := -1;
    e8 := f7_v - 1/kd_8 * u7_d * d7_d;
    proj8to7, incl7to8 := DecomposeIdem(e8);
    e8red := proj8to7 * e8 * incl7to8;
    incl4to8 := Tensor(act, incl4to7, [id,v]) * incl7to8;
    proj8to4 := proj8to7 * Tensor(act, proj7to4, [id,v]);
    incl1to8 := Tensor(act, incl1to7, [id,v]) * incl7to8;
    proj8to1 := proj8to7 * Tensor(act, proj7to1, [id,v]);

    e9 := Tensor(act,e8red,BSId(B,2)`stdmor);
    proj9to8, incl8to9 := DecomposeIdem(e9);
    e9red := proj9to8 * e9 * incl8to9;
    incl4to9 := Tensor(act, incl4to8, [id,t]) * incl8to9;
    proj9to4 := proj9to8 * Tensor(act, proj8to4, [id,t]);
    incl1to9 := Tensor(act, incl1to8, [id,t]) * incl8to9;
    proj9to1 := proj9to8 * Tensor(act, proj8to1, [id,t]);

    //e9 x 1 = e10 + e8 + ed
    f9_s := Tensor(act, e9red, [id,s]);
    br9to8 := (Braid(B,4,1) cat [3,4]) * ([4] cat Braid(B,3,1) cat [4]) * ([4,3] cat Braid(B,4,1));
    br8to9 := ([4,3] cat Braid(B,1,4)) * ([4] cat Braid(B,1,3) cat [4]) * (Braid(B,1,4) cat [3,4]);
    d9_8 := e8red * proj8to4 * Tensor(act, e4red, br9to8`stdmor) * Tensor(act, e4red, LocalisedLLDown(B,[1,4,3,4,2,1],[1,1,1,1,0,0])) * Tensor(act, incl4to9, BSId(B,1)`stdmor) * f9_s;
    u9_8 := f9_s * Tensor(act, proj9to4, BSId(B,1)`stdmor) * Tensor(act, e4red, LocalisedLLUp(B,[1,4,3,4,2,1],[1,1,1,1,0,0])) * Tensor(act, e4red, br8to9`stdmor) * incl4to8 * e8red;
    b8_10 := d9_8 * u9_8;
    k8_10 := Matrix(b8_10)[1,1]/Matrix(e8red)[1,1];
    //k8_10 := -f.1;
    br9to6 := ([1,2,1,2] cat Braid(B,4,1)) * ([1,2,1] cat Braid(B,4,2) cat [1]) * ([1,2] cat Braid(B,4,1) cat [2,1]) * ([1] cat Braid(B,4,2) cat [1,2,1]) * (Braid(B,4,1) cat [2,1,2,1]); 
    br6to9 := (Braid(B,1,4) cat [2,1,2,1]) * ([1] cat Braid(B,2,4) cat [1,2,1])  * ([1,2] cat Braid(B,1,4) cat [2,1]) *  ([1,2,1] cat Braid(B,2,4) cat [1]) * ([1,2,1,2] cat Braid(B,1,4)); 
    d9_d := e6red * proj6to1 * br9to6`stdmor * LocalisedLLDown(B,[1,2,1,2,1,4,3,4,2,1],[1,1,1,1,1,0,0,1,0,0]) * Tensor(act, incl1to9, BSId(B,1)`stdmor) * f9_s;
    u9_d := f9_s * Tensor(act, proj9to1, BSId(B,1)`stdmor) * LocalisedLLUp(B,[1,2,1,2,1,4,3,4,2,1],[1,1,1,1,1,0,0,1,0,0]) * br6to9`stdmor * incl1to6 * e6red;
    bd_10 := d9_d * u9_d;
    kd_10 := Matrix(bd_10)[1,1]/Matrix(e6red)[1,1];
    //kd_10 := f.1;
    e10 := f9_s - 1/k8_10 * u9_8 * d9_8 - 1/kd_10 * u9_d * d9_d;
    proj10to9, incl9to10 := DecomposeIdem(e10);
    e10red := proj10to9 * e10 * incl9to10;
    incl8to10 := Tensor(act, incl8to9, [id,s]) * incl9to10;
    proj10to8 := proj10to9 * Tensor(act, proj9to8, [id,s]);

    //e10 x 2 = e11 + e9
    f10_t := Tensor(act, e10red, [id,t]);
    d10_9 := e9red * proj9to8 * Tensor(act, e8red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl8to10, BSId(B,2)`stdmor) * f10_t;
    u10_9 := f10_t * Tensor(act, proj10to9, BSId(B,2)`stdmor) * Tensor(act, e8red, LocalisedLLUp(B,[2,1,2],[1,0,0])) * incl8to9 * e9red;
    b9_11 := d10_9 * u10_9;
    k9_11 := Matrix(b9_11)[1,1]/Matrix(e9)[1,1];
    //k9_11 := -1;
    e11 := f10_t - 1/k9_11 * u10_9 * d10_9;
    proj11to10, incl10to11 := DecomposeIdem(e11);
    e11red := proj11to10 * e11 * incl10to11;
    incl9to11 := Tensor(act, incl9to10, [id,t]) * incl10to11;
    proj11to9 := proj11to10 * Tensor(act, proj10to9, [id,t]);

    //e11 x 1 = e12 + e10
    f11_s := Tensor(act, e11red, [id,s]);
    d11_10 := e10red * proj10to9 * Tensor(act, e9red, LocalisedLLDown(B,[1,2,1],[1,0,0])) * Tensor(act, incl9to11, BSId(B,1)`stdmor) * f11_s;
    u11_10 := f11_s * Tensor(act, proj11to9, BSId(B,1)`stdmor) * Tensor(act, e9red, LocalisedLLUp(B,[1,2,1],[1,0,0])) * incl9to10 * e10red;
    b10_12 := d11_10 * u11_10;
    k10_12 := Matrix(b10_12)[1,1]/Matrix(e10red)[1,1];
    //k10_12 := -f.1+1;
    e12 := f11_s - 1/k10_12 * u11_10 * d11_10;
    proj12to11, incl11to12 := DecomposeIdem(e12);
    e12red := proj12to11 * e12 * incl11to12;

    //flip
    eflip2 := Tensor(act,[id,t],e1);

    //1 x eflip2 = eflip3 + eflip1
    fflip2_s := Tensor(act, [id,s], eflip2);
    dflip2_1 := e1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * fflip2_s;
    uflip2_1 := fflip2_s * LocalisedLLUp(B,[1,2,1],[1,0,0]) * e1;
    kflip1_3 := -f.1;
    eflip3 := fflip2_s - 1/kflip1_3 * uflip2_1 * dflip2_1;

    //2 x eflip3 = eflip4 + eflip2
    fflip3_t := Tensor(act, [id,t], eflip3);
    dflip3_2 := eflip2 * LocalisedLLDown(B,[2,1,2,1],[1,0,0,1]) * fflip3_t;
    uflip3_2 := fflip3_t * LocalisedLLUp(B,[2,1,2,1],[1,0,0,1]) * eflip2;
    kflip2_4 := -1;
    eflip4 := fflip3_t - 1/kflip2_4 * uflip3_2 * dflip3_2;
    projflip4to1, inclflip1to4 := DecomposeIdem(eflip4);
    eflip4red := projflip4to1 * eflip4 * inclflip1to4;

    //1 x eflip4 = eflip5 + eflip3
    fflip4_s := Tensor(act, [id,s], eflip4red);
    dflip4_3 := eflip3 * LocalisedLLDown(B,[1,2,1,2,1],[1,0,0,1,1]) * Tensor(act, BSId(B,1)`stdmor, inclflip1to4) * fflip4_s;
    uflip4_3 := fflip4_s * Tensor(act, BSId(B,1)`stdmor, projflip4to1) * LocalisedLLUp(B,[1,2,1,2,1],[1,0,0,1,1]) * eflip3;
    kflip3_5 := -f.1+1;
    eflip5 := fflip4_s - 1/kflip3_5 * uflip4_3 * dflip4_3;
    projflip5to4, inclflip4to5 := DecomposeIdem(eflip5);
    eflip5red := projflip5to4 * eflip5 * inclflip4to5;
    inclflip1to5 := Tensor(act, [id,s], inclflip1to4) * inclflip4to5;
    projflip5to1 := projflip5to4 * Tensor(act, [id,s], projflip4to1);

    eflip6 := Tensor(act, BSId(B,4)`stdmor, eflip5red);
    projflip6to5, inclflip5to6 := DecomposeIdem(eflip6);
    eflip6red := projflip6to5 * eflip6 * inclflip5to6;
    inclflip4to6 := Tensor(act, [id,v], inclflip4to5) * inclflip5to6;
    projflip6to4 := projflip6to5 * Tensor(act, [id,v], projflip5to4);
    inclflip1to6 := Tensor(act, [id,v], inclflip1to5) * inclflip5to6;
    projflip6to1 := projflip6to5 * Tensor(act, [id,v], projflip5to1);

    eflip7 := Tensor(act, BSId(B,3)`stdmor, eflip6red);
    projflip7to6, inclflip6to7 := DecomposeIdem(eflip7);
    eflip7red := projflip7to6 * eflip7 * inclflip6to7;
    inclflip4to7 := Tensor(act, [id,u], inclflip4to6) * inclflip6to7;
    projflip7to4 := projflip7to6 * Tensor(act, [id,u], projflip6to4);
    inclflip1to7 := Tensor(act, [id,u], inclflip1to6) * inclflip6to7;
    projflip7to1 := projflip7to6 * Tensor(act, [id,u], projflip6to1);

    //4 x eflip7 = eflip8 + eflip6
    fflip7_v := Tensor(act, [id,v], eflip7red);
    dflip7_6 := eflip6red * projflip6to4 * Tensor(act, LocalisedLLDown(B,[4,3,4,1],[1,0,0,1]), eflip4red) * Tensor(act, BSId(B,[4])`stdmor, inclflip4to7) * fflip7_v;
    uflip7_6 := fflip7_v * Tensor(act, BSId(B,[4])`stdmor, projflip7to4) * Tensor(act, LocalisedLLUp(B,[4,3,4,1],[1,0,0,1]), eflip4red) * inclflip4to6 * eflip6red;
    kflipd_8 := -1;
    eflip8 := fflip7_v - 1/kflipd_8 * uflip7_6 * dflip7_6;
    projflip8to7, inclflip7to8 := DecomposeIdem(eflip8);
    eflip8red := projflip8to7 * eflip8 * inclflip7to8;
    inclflip4to8 := Tensor(act, [id,v], inclflip4to7) * inclflip7to8;
    projflip8to4 := projflip8to7 * Tensor(act, [id,v], projflip7to4);
    inclflip1to8 := Tensor(act, [id,v], inclflip1to7) * inclflip7to8;
    projflip8to1 := projflip8to7 * Tensor(act, [id,v], projflip7to1);

    eflip9 := Tensor(act, BSId(B,2)`stdmor, eflip8red);
    projflip9to8, inclflip8to9 := DecomposeIdem(eflip9);
    eflip9red := projflip9to8 * eflip9 * inclflip8to9;
    inclflip4to9 := Tensor(act, [id,t], inclflip4to8) * inclflip8to9;
    projflip9to4 := projflip9to8 * Tensor(act, [id,t], projflip8to4);
    inclflip1to9 := Tensor(act, [id,t], inclflip1to8) * inclflip8to9;
    projflip9to1 := projflip9to8 * Tensor(act, [id,t], projflip8to1);

    //1 x eflip9 = eflip10 + eflip8 + eflip6
    fflip9_s := Tensor(act, [id,s], eflip9red);
    dflip9_8 := eflip8red * projflip8to4 * Tensor(act, LocalisedLLDown(B,[1,2,4,3,4,1],[1,0,1,1,1,0]), eflip4red) * Tensor(act, BSId(B,1)`stdmor, inclflip4to9) * fflip9_s;
    uflip9_8 := fflip9_s * Tensor(act, BSId(B,1)`stdmor, projflip9to4) * Tensor(act, LocalisedLLUp(B,[1,2,4,3,4,1],[1,0,1,1,1,0]), eflip4red) * inclflip4to8 * eflip8red;
    kflip8_10 := -f.1;
    dflip9_6 := eflip6red * projflip6to1 * LocalisedLLDown(B,[1,2,4,3,4,1,2,1,2,1],[1,1,0,0,1,1,1,1,0,0]) * Tensor(act, BSId(B,1)`stdmor, inclflip1to9) * fflip9_s;
    uflip9_6 := fflip9_s * Tensor(act, BSId(B,1)`stdmor, projflip9to1) * LocalisedLLUp(B,[1,2,4,3,4,1,2,1,2,1],[1,1,0,0,1,1,1,1,0,0]) * inclflip1to6 * eflip6red;
    kflip6_10 := f.1;
    eflip10 := fflip9_s - 1/kflip8_10 * uflip9_8 * dflip9_8 - 1/kflip6_10 * uflip9_6 * dflip9_6;
    projflip10to9, inclflip9to10 := DecomposeIdem(eflip10);
    eflip10red := projflip10to9 * eflip10 * inclflip9to10;
    inclflip8to10 := Tensor(act, [id,s], inclflip8to9) * inclflip9to10;
    projflip10to8 := projflip10to9 * Tensor(act, [id,s], projflip9to8);

    //2 x eflip10 = eflip11 + eflip9
    fflip10_t := Tensor(act, [id,t], eflip10red);
    dflip10_9 := eflip9red * projflip9to8 * Tensor(act, LocalisedLLDown(B,[2,1,2],[1,0,0]), eflip8red) * Tensor(act, BSId(B,2)`stdmor, inclflip8to10) * fflip10_t;
    uflip10_9 := fflip10_t * Tensor(act, BSId(B,2)`stdmor, projflip10to8) * Tensor(act, LocalisedLLUp(B,[2,1,2],[1,0,0]), eflip8red) * inclflip8to9 * eflip9red;
    kflip9_11 := -1;
    eflip11 := fflip10_t - 1/kflip9_11 * uflip10_9 * dflip10_9;
    projflip11to10, inclflip10to11 := DecomposeIdem(eflip11);
    eflip11red := projflip11to10 * eflip11 * inclflip10to11;
    inclflip9to11 := Tensor(act, [id,t], inclflip9to10) * inclflip10to11;
    projflip11to9 := projflip11to10 * Tensor(act, [id,t], projflip10to9);

    //1 x eflip11 = eflip12 + eflip10
    fflip11_s := Tensor(act, [id,s], eflip11red);
    dflip11_10 := eflip10red * projflip10to9 * Tensor(act, LocalisedLLDown(B,[1,2,1],[1,0,0]), eflip9red) * Tensor(act, BSId(B,1)`stdmor, inclflip9to11) * fflip11_s;
    uflip11_10 := fflip11_s * Tensor(act, BSId(B,1)`stdmor, projflip11to9) * Tensor(act, LocalisedLLUp(B,[1,2,1],[1,0,0]), eflip9red) * inclflip9to10 * eflip10red;
    kflip10_12 := -f.1+1;
    eflip12 := fflip11_s - 1/kflip10_12 * uflip11_10 * dflip11_10;
    projflip12to11, inclflip11to12 := DecomposeIdem(eflip12);
    eflip12red := projflip12to11 * eflip12 * inclflip11to12;

    //Dimension:

    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
    
    //trace for e12:

    //For dim(d) one can use lightleaves
    d_top := proj6to1 * br9to6`stdmor * LocalisedLLDown(B,[1,2,1,2,1,4,4,1,2,1,2,1],[1,1,1,1,1,1,0,0,0,0,0,0]) * Tensor(act, incl1to6, inclflip1to6);
    d_bot := Tensor(act, proj6to1, projflip6to1) * LocalisedLLUp(B,[1,2,1,2,1,4,4,1,2,1,2,1],[1,1,1,1,1,1,0,0,0,0,0,0]) * br6to9`stdmor * incl1to6;
    trace_d := d_top * Tensor(act, e6red, root^6*eflip6red) * d_bot;
    //The result is 300*f.1+180. Therefore need to scale other traces by that amount.
    dim_d := trace_d`mat[1,1]/trace_d`mat[1,1];
    Sprintf("The dimension of d=121214 is %o", dim_d);

    //partial trace around e12 x eflip12
    top6map := Tensor(act, e6red, Tensor(act, Cap(B,3)`stdmor, eflip6red)) * Tensor(act, incl6to7, inclflip6to7);
    bot6map := Tensor(act, proj7to6, projflip7to6) * Tensor(act, e6red, Tensor(act, Cup(B,3)`stdmor, eflip6red));
    t6 := top6map;
    b6 := bot6map;

    top5map := Tensor(act, e7red, Tensor(act, Cap(B,4)`stdmor, eflip7red)) * Tensor(act, incl7to8, inclflip7to8);
    bot5map := Tensor(act, proj8to7, projflip8to7) * Tensor(act, e7red, Tensor(act, Cup(B,4)`stdmor, eflip7red));  
    t5 := t6 * top5map;
    b5 := bot5map * b6;

    top4map := Tensor(act, e8red, Tensor(act, Cap(B,2)`stdmor, eflip8red)) * Tensor(act, incl8to9, inclflip8to9);
    bot4map := Tensor(act, proj9to8, projflip9to8) * Tensor(act, e8red, Tensor(act, Cup(B,2)`stdmor, eflip8red));
    t4 := t5 * top4map;
    b4 := bot4map * b5;

    top3map := Tensor(act, e9red, Tensor(act, Cap(B,1)`stdmor, eflip9red)) * Tensor(act, incl9to10, inclflip9to10);
    bot3map := Tensor(act, proj10to9, projflip10to9) * Tensor(act, e9red, Tensor(act, Cup(B,1)`stdmor, eflip9red));
    t3 := t4 * top3map;
    b3 := bot3map * b4;

    top2map := Tensor(act, e10red, Tensor(act, Cap(B,2)`stdmor, eflip10red)) * Tensor(act, incl10to11, inclflip10to11);
    bot2map := Tensor(act, proj11to10, projflip11to10) * Tensor(act, e10red, Tensor(act, Cup(B,2)`stdmor, eflip10red));  
    t2 := t3 * top2map;
    b2 := bot2map * b3;

    top1map := Tensor(act, e11red, Tensor(act, Cap(B,1)`stdmor, eflip11red)) * Tensor(act, incl11to12, inclflip11to12);
    bot1map := Tensor(act, proj12to11, projflip12to11) * Tensor(act, e11red, Tensor(act, Cup(B,1)`stdmor, eflip11red));
    t1 := t2 * top1map;
    b1 := bot1map * b2;

    t0 := d_top * t1;
    b0 := b1 * d_bot;
    //This is the longest calculation
    middle := Tensor(act, e12red, root^6*eflip12red);
   
    //then compute dimension
    trace_w := t0 * middle * b0;

    dim_w := trace_w`mat[1,1]/trace_d`mat[1,1];
    Sprintf("The dimension of w1=121214342121 is %o", dim_w);
    //Result is 1740*f.1+1080
    
    T := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("The total time for the calculation took %o, used space was %o.", T, S);
end procedure;

procedure H4_middle_19()
    //Case A19
    ResetMaximumMemoryUsage();
    T := Time();

    AttachSpec("ASLoc.spec");
    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");

    f := BaseRing(carH4);
    FR := RationalFunctionField(f,Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [ hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    FA := B`FAct;

    act := function(w)
        return FActionByElt(B,w);
    end function;

    id := W.0;
    s := W.1;
    t := W.2;
    u := W.3;
    v := W.4;
    
    //we have x1 := 1212132121; d=x2 := 12121321213212; x3:= (x1)432121
    //We choose the shorthand e1 to e14 for the words up to d and take the construction from the H3 case
    //At x1 the plethysm graphs branches out; for x3 we choose the labelling 111 to 116;
    
    e1 := BSId(B,1)`stdmor;

    e2 := Tensor(act,e1,[id,t]);

    //e2 x 1 = e3 + e1
    f2_s := Tensor(act, e2, [id,s]);
    d2_1 := e1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * f2_s;
    u2_1 := f2_s * LocalisedLLUp(B,[1,2,1],[1,0,0]) * e1;
    b1_3 := d2_1 * u2_1;
    k1_3 := Matrix(b1_3)[1,1] / Matrix(e1)[1,1];
    //k1_3 := -f.1;
    e3 := f2_s - 1/k1_3 * u2_1 * d2_1;
    proj3to1, incl1to3 := DecomposeIdem(e3);
    e3red := proj3to1 * e3 * incl1to3;

    //e4:
    f3_t := Tensor(act, e3red, [id,t]);
    incl3_t := Tensor(act, incl1to3, [id,t]);
    proj3_t := Tensor(act, proj3to1, [id,t]);
    d3_2 := e2 * LocalisedLLDown(B,[1,2,1,2],[1,1,0,0]) * incl3_t * f3_t;
    u3_2 := f3_t * proj3_t * LocalisedLLUp(B,[1,2,1,2],[1,1,0,0]) * e2;
    b2_4 := d3_2 * u3_2;
    k2_4 := Matrix(b2_4)[1,1] / Matrix(e2)[1,1];
    //k2_4 := -1;
    e4 := f3_t - 1/k2_4 * u3_2 * d3_2;
   
    proj4to3, incl3to4 := DecomposeIdem(e4);
    e4red := proj4to3 * e4 * incl3to4;
    incl1to4 := Tensor(act, incl1to3, [id,t]) * incl3to4;
    proj4to1 := proj4to3 * Tensor(act, proj3to1, [id,t]);

    //e5:
    f4_s := Tensor(act, e4red, [id,s]);
    d4_3 := e3red * proj3to1 * (Tensor(act, e2, LocalisedLLDown(B,[1,2,1],[1,0,0]))) * Tensor(act, incl1to4, [id,s]) * f4_s;
    u4_3 := f4_s * Tensor(act, proj4to1, [id,s]) * Tensor(act, e2, LocalisedLLUp(B,[1,2,1],[1,0,0])) * incl1to3 * e3red;
    b3_5 := d4_3 * u4_3;
    k3_5 := Matrix(b3_5)[1,1] / Matrix(e3red)[1,1];
    //k3_5 := -f.1 +1;
    e5 := f4_s - 1/k3_5 * u4_3 * e3red * d4_3;
    proj5to4, incl4to5 := DecomposeIdem(e5);

    e5red := proj5to4 * e5 * incl4to5;
    incl1to5 := Tensor(act, incl1to4, [id,s]) * incl4to5;
    proj5to1 := proj5to4 * Tensor(act, proj4to1, [id,s]);
    incl3to5 := Tensor(act, incl3to4, [id,s]) * incl4to5;
    proj5to3 := proj5to4 * Tensor(act, proj4to3, [id,s]);

    //e6:
    e6 := Tensor(act, e5red, [id,u]);
    proj6to5, incl5to6 := DecomposeIdem(e6);
    e6red := proj6to5 * e6 * incl5to6;

    incl1to6 := Tensor(act, incl1to5, [id,u]) * incl5to6;
    proj6to1 := proj6to5 * Tensor(act, proj5to1, [id,u]);
    incl4to6 := Tensor(act, incl4to5, [id,u]) * incl5to6;
    proj6to4 := proj6to5 * Tensor(act, proj5to4, [id,u]);

    //e7:
    f6_t := Tensor(act, e6red, [id,t]);
    br6to5 := (Braid(B,1,2) cat [3,2])`stdmor;
    br5from6 := (Braid(B,2,1))`stdmor;
    br5to6 := (Braid(B,1,2))`stdmor;
    br6from5 := (Braid(B,2,1) cat [3,2])`stdmor;
    d6_5 := e5red * proj5to1 * br5from6 * LocalisedLLDown(B,[2,1,2,1,2,3,2],[1,1,1,1,1,0,0]) * br6to5 * Tensor(act, incl1to6, [id,t]) * f6_t;
    u6_5 := f6_t * Tensor(act, proj6to1, [id,t]) * br6from5 * LocalisedLLUp(B,[2,1,2,1,2,3,2],[1,1,1,1,1,0,0]) * br5to6 * incl1to5 * e5red;

    b5_7 := d6_5 * u6_5;
    k5_7 := Matrix(b5_7)[1,1] / Matrix(e5red)[1,1];
    //k5_7 := -1;
    e7 := f6_t - 1/k5_7 * u6_5 * d6_5;
    proj7to6, incl6to7 := DecomposeIdem(e7);
    e7red := proj7to6 * e7 * incl6to7;
    
    incl1to7 := Tensor(act, incl1to6, [id,t]) * incl6to7;
    proj7to1 := proj7to6 * Tensor(act, proj6to1, [id,t]);
    incl5to7 := Tensor(act, incl5to6, [id,t]) * incl6to7;
    proj7to5 := proj7to6 * Tensor(act, proj6to5, [id,t]);
    incl4to7 := Tensor(act, incl4to6, [id,t]) * incl6to7;
    proj7to4 := proj7to6 * Tensor(act, proj6to4, [id,t]);

    //e8:
    f7_s := Tensor(act, e7red, [id,s]);
    //We include e7red into e4\otimes 132 so that we can braid in the end; then tensor with s, apply light leave, braid back and project back onto e7red
    d7_6 := proj6to4 * Tensor(act, e4red, Braid(B,3,1)`stdmor) * Tensor(act, e4red, LocalisedLLDown(B,[3,1,2,1],[1,1,0,0])) * Tensor(act, Tensor(act, Tensor(act, e4red, Braid(B,1,3)`stdmor), [id,t]) * incl4to7 ,[id,s]) * f7_s;                     
    u7_6 := f7_s * Tensor(act, proj7to4 * Tensor(act, Tensor(act, e4red, Braid(B,3,1)`stdmor), [id,t]),[id,s]) * Tensor(act, e4red, LocalisedLLUp(B,[3,1,2,1],[1,1,0,0])) * Tensor(act, e4red, Braid(B,1,3)`stdmor) * incl4to6;
    b6_8 := d7_6 * u7_6;
    k6_8 := Matrix(b6_8)[1,1] / Matrix(e6red)[1,1];
    //k6_8 := -f.1;
    e8 := f7_s - 1/k6_8 * u7_6 * d7_6;
    proj8to7, incl7to8 := DecomposeIdem(e8);
    e8red := proj8to7 * e8 * incl7to8;
    incl6to8 := Tensor(act, incl6to7, [id,s]) * incl7to8;
    proj8to6 := proj8to7 * Tensor(act, proj7to6, [id,s]);
    incl1to8 := Tensor(act, incl1to7, [id,s]) * incl7to8;
    proj8to1 := proj8to7 * Tensor(act, proj7to1, [id,s]);
    incl5to8 := Tensor(act, incl5to7, [id,s]) * incl7to8;
    proj8to5 := proj8to7 * Tensor(act, proj7to5, [id,s]);
    incl4to8 := Tensor(act, incl4to7, [id,s]) * incl7to8;
    proj8to4 := proj8to7 * Tensor(act, proj7to4, [id,s]);

    //e9:
    //f8_t := Tensor(act, e8red, [id,t]);
    d8_7 := proj7to6 * Tensor(act, e6red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl6to8, [id,t]);
    u8_7 := Tensor(act, proj8to6, [id,t]) * Tensor(act, e6red, LocalisedLLUp(B,[2,1,2],[1,0,0])) * incl6to7;
    b7_9 := d8_7 * u8_7;
    k7_9 := Matrix(b7_9)[1,1] / Matrix(e7red)[1,1];
    //k7_9 := -1; 
    e9 := Tensor(act, e8red, [id,t]) - 1/k7_9 * u8_7 * d8_7;
    proj9to8, incl8to9 := DecomposeIdem(e9);
    e9red := proj9to8 * e9 * incl8to9;
    incl7to9 := Tensor(act, incl7to8, [id,t]) * incl8to9;
    proj9to7 := proj9to8 * Tensor(act, proj8to7, [id,t]);
    incl1to9 := Tensor(act, incl1to8, [id,t]) * incl8to9;
    proj9to1 := proj9to8 * Tensor(act, proj8to1, [id,t]);
    incl5to9 := Tensor(act, incl5to8, [id,t]) * incl8to9;
    proj9to5 := proj9to8 * Tensor(act, proj8to5, [id,t]);
    incl4to9 := Tensor(act, incl4to8, [id,t]) * incl8to9;
    proj9to4 := proj9to8 * Tensor(act, proj8to4, [id,t]);

    //e10
    //f9_s := Tensor(act, e9red, [id,s]);
    d9_8 := proj8to7 * Tensor(act, e7red, LocalisedLLDown(B,[1,2,1],[1,0,0])) * Tensor(act, incl7to9, [id,s]);
    u9_8 := Tensor(act, proj9to7, [id,s]) * Tensor(act, e7red, LocalisedLLUp(B,[1,2,1],[1,0,0])) * incl7to8;
    b8_10 := d9_8 * u9_8;
    k8_10 := Matrix(b8_10)[1,1] / Matrix(e8red)[1,1];
    //k8_10 := -f.1+1;
    e10 := Tensor(act, e9red, [id,s]) - 1/k8_10 * u9_8 * d9_8;
    proj10to9, incl9to10 := DecomposeIdem(e10);
    e10red := proj10to9 * e10 * incl9to10;
    incl5to10 := Tensor(act, incl5to9, [id,s]) * incl9to10;
    proj10to5 := proj10to9 * Tensor(act, proj9to5, [id,s]);
    incl4to10 := Tensor(act, incl4to9, [id,s]) * incl9to10;
    proj10to4 := proj10to9 * Tensor(act, proj9to4, [id,s]);
    incl1to10 := Tensor(act, incl1to9, [id,s]) * incl9to10;
    proj10to1 := proj10to9 * Tensor(act, proj9to1, [id,s]);
    incl8to10 := Tensor(act, incl8to9, [id,s]) * incl9to10;
    proj10to8 := proj10to9 * Tensor(act, proj9to8, [id,s]);

    //ex
    br9to8 := (([2,1,2,1,3,2] cat Braid(B,3,1) cat [2]) * ([2,1,2,1] cat Braid(B,2,3) cat[1,2]) * (Braid(B,1,2) cat [3,2,1,2]))`stdmor;
    br9from8 := ((Braid(B,2,1) cat [3,2,1,2]) * ([2,1,2,1] cat Braid(B,3,2) cat[1,2]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2]))`stdmor;
    br8from9 :=  ((Braid(B,2,1) cat [3,2,1]) * ([2,1,2,1] cat Braid(B,3,2) cat[1]) * ([2,1,2,1,3,2] cat Braid(B,1,3)))`stdmor;
    br8to9 := (([2,1,2,1,3,2] cat Braid(B,3,1)) * ([2,1,2,1] cat Braid(B,2,3) cat[1]) * (Braid(B,1,2) cat [3,2,1]))`stdmor;

    dx_8 := proj8to1 * br8from9 * LocalisedLLDown(B,[2,1,2,1,3,2,1,3,2,3],[1,1,1,1,1,1,1,1,0,0]) * Tensor(act, br9to8 * incl1to9, [id,u]);
    ux_8 := Tensor(act, proj9to1 * br9from8, [id,u]) * LocalisedLLUp(B,[2,1,2,1,3,2,1,3,2,3],[1,1,1,1,1,1,1,1,0,0]) * br8to9 * incl1to8;

    b8_x := dx_8 * ux_8;
    k8_x := Matrix(b8_x)[1,1] / Matrix(e8red)[1,1];
    //k8_x := -1;
    ex := Tensor(act, e9red, [id,u]) - 1/k8_x * ux_8 * dx_8;
    projxto9, incl9tox := DecomposeIdem(ex);
    exred := projxto9 * ex * incl9tox;
    incl1tox := Tensor(act, incl1to9, [id,u]) * incl9tox;
    projxto1 := projxto9 * Tensor(act, proj9to1, [id,u]);

    //e11:
    e11 := Tensor(act, e10red, [id,u]);
    proj11to10, incl10to11 := DecomposeIdem(e11);
    e11red := proj11to10 * e11 * incl10to11;
    incl9to11 := Tensor(act, incl9to10, [id,u]) * incl10to11;
    proj11to9 := proj11to10 * Tensor(act, proj10to9, [id,u]);
    incl5to11 := Tensor(act, incl5to10, [id,u]) * incl10to11;
    proj11to5 := proj11to10 * Tensor(act, proj10to5, [id,u]);
    incl4to11 := Tensor(act, incl4to10, [id,u]) * incl10to11;
    proj11to4 := proj11to10 * Tensor(act, proj10to4, [id,u]);
    incl1to11 := Tensor(act, incl1to10, [id,u]) * incl10to11;
    proj11to1 := proj11to10 * Tensor(act, proj10to1, [id,u]);

    //e12:
    //For 12 we now have two summands. This is the most messy calculation
    br11to10 := Tensor(act, e4red, (([3] cat Braid(B,1,2) cat [3]) * (Braid(B,1,3) cat [2,1,2,1,3]))`stdmor);
    br10to11 := Tensor(act, e4red, (([3] cat Braid(B,1,2)) * (Braid(B,1,3) cat [2,1,2,1]))`stdmor);
    br11from10 := Tensor(act, e4red, ((Braid(B,3,1) cat [2,1,2,1,3]) * ([3] cat Braid(B,2,1) cat [3]))`stdmor);
    br10from11 := Tensor(act, e4red, ((Braid(B,3,1) cat [2,1,2,1]) * ([3] cat Braid(B,2,1)))`stdmor);

    d11_10 := proj10to4 * br10from11 *  Tensor(act, e4red, LocalisedLLDown(B,[3,2,1,2,1,2,3,2],[1,1,1,1,1,1,0,0]))  * Tensor(act, br11to10 * incl4to11, [id,t]);
    u11_10 := Tensor(act, proj11to4 * br11from10, [id,t]) * Tensor(act, e4red, LocalisedLLUp(B,[3,2,1,2,1,2,3,2],[1,1,1,1,1,1,0,0])) * br10to11 * incl4to10;
    b10_12 := d11_10 * u11_10;
    k10_12 := Matrix(b10_12)[1,1] / Matrix(e10red)[1,1];
    //k10_12 := -1;

    br11tox := (([2,1,2,1,3,2,1] cat Braid(B,3,2) cat [1]) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2] cat Braid(B,1,3)) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2,1,3]) * (Braid(B,1,2) cat [3,2,1,2,1,3]))`stdmor;
    brxto11 := (([2,1,2,1,3,2,1] cat Braid(B,3,2)) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2,3]) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2,3]) * (Braid(B,1,2) cat [3,2,1,2,3]))`stdmor;
    br11fromx := (((Braid(B,2,1) cat [3,2,1,2,1,3]) * [2,1,2,1] cat Braid(B,3,2) cat [1,2,1,3]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2] cat Braid(B,3,1)) * ([2,1,2,1,3,2,1] cat Braid(B,2,3) cat [1]))`stdmor;
    brxfrom11 := (((Braid(B,2,1) cat [3,2,1,2,3]) * [2,1,2,1] cat Braid(B,3,2) cat [1,2,3]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2,3]) * ([2,1,2,1,3,2,1] cat Braid(B,2,3)))`stdmor;
    d11_x := projxto1 * brxfrom11 *  LocalisedLLDown(B,[2,1,2,1,3,2,1,2,3,2,1,2],[1,1,1,1,1,1,1,1,1,1,0,0])  * Tensor(act, br11tox * incl1to11, [id,t]);
    u11_x := Tensor(act, proj11to1 * br11fromx, [id,t]) * LocalisedLLUp(B,[2,1,2,1,3,2,1,2,3,2,1,2],[1,1,1,1,1,1,1,1,1,1,0,0]) * brxto11 * incl1tox;
    bx_12 := d11_x * u11_x;
    kx_12 := Matrix(bx_12)[1,1] / Matrix(exred)[1,1];
    //kx_12 := -f.1;

    e12 := Tensor(act, e11red, [id,t]) - 1/k10_12 * u11_10 * d11_10 - 1/kx_12 * u11_x * d11_x;
    proj12to11, incl11to12 := DecomposeIdem(e12);
    e12red := proj12to11 * e12 * incl11to12;
    incl10to12 := Tensor(act, incl10to11, [id,t]) * incl11to12;
    proj12to10 := proj12to11 * Tensor(act, proj11to10, [id,t]);
    incl9to12 := Tensor(act, incl9to11, [id,t]) * incl11to12;
    proj12to9 := proj12to11 * Tensor(act, proj11to9, [id,t]);
    incl1to12 := Tensor(act, incl1to11, [id,t]) * incl11to12;
    proj12to1 := proj12to11 * Tensor(act, proj11to1, [id,t]);

    //e13
    br12to11 := Tensor(act, e9red, (Braid(B,1,3) cat [2])`stdmor);
    br11to12 := Tensor(act, e9red, (Braid(B,1,3))`stdmor);
    br12from11 := Tensor(act, e9red, (Braid(B,3,1) cat [2])`stdmor);
    br11from12 := Tensor(act, e9red, (Braid(B,3,1))`stdmor);

    d12_11 := proj11to9 * br11from12 *  Tensor(act, e9red, LocalisedLLDown(B,[3,1,2,1],[1,1,0,0])) * Tensor(act, br12to11 * incl9to12, [id,s]);
    u12_11 := Tensor(act, proj12to9 * br12from11, [id,s]) * Tensor(act, e9red, LocalisedLLUp(B,[3,1,2,1],[1,1,0,0])) * br11to12 * incl9to11;

    b11_13 := d12_11 * u12_11;
    k11_13 := Matrix(b11_13)[1,1] / Matrix(e11red)[1,1];
    //k11_13 := -1;

    e13 := Tensor(act, e12red, [id,s]) - 1/k11_13 * u12_11 * d12_11;
    proj13to12, incl12to13 := DecomposeIdem(e13);
    e13red := proj13to12 * e13 * incl12to13;
    incl11to13 := Tensor(act, incl11to12, [id,s]) * incl12to13;
    proj13to11 := proj13to12 * Tensor(act, proj12to11, [id,s]);
    incl1to13 := Tensor(act, incl1to12, [id,s]) * incl12to13;
    proj13to1 := proj13to12 * Tensor(act, proj12to1, [id,s]);

    //e14 = ex2
    d13_12 := proj12to11 * Tensor(act, e11red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl11to13, [id,t]);
    u13_12 := Tensor(act, proj13to11, [id,t]) * Tensor(act, e11red, LocalisedLLUp(B,[2,1,2],[1,0,0])) * incl11to12;

    b12_14 := d13_12 * u13_12;
    k12_14 := Matrix(b12_14)[1,1] / Matrix(e12red)[1,1];
    //k12_14 := -f.1 + 1;
    e14 := Tensor(act, e13red, [id,t]) - 1/k12_14 * u13_12 * d13_12;
    proj14to13, incl13to14 := DecomposeIdem(e14);
    e14red := proj14to13 * e14 * incl13to14;
    incl1to14 := Tensor(act, incl1to13, [id,t]) * incl13to14;
    proj14to1 := proj14to13 * Tensor(act, proj13to1, [id,t]);
    
    //e10 x 4 = e111
    e111 := Tensor(act, e10red, [id,v]);
    proj111to10, incl10to111 := DecomposeIdem(e111);
    e111red := proj111to10 * e111 * incl10to111;
    incl9to111 := Tensor(act, incl9to10, [id,v]) * incl10to111;
    proj111to9 := proj111to10 * Tensor(act, proj10to9, [id,v]);
    incl4to111 := Tensor(act, incl4to10, [id,v]) * incl10to111;
    proj111to4 := proj111to10 * Tensor(act, proj10to4, [id,v]);
    incl1to111 := Tensor(act, incl1to10, [id,v]) * incl10to111;
    proj111to1 := proj111to10 * Tensor(act, proj10to1, [id,v]);
    
    //e111 x 3 = e112
    e112 := Tensor(act, e111red, [id,u]);
    proj112to111, incl111to112 := DecomposeIdem(e112);
    e112red := proj112to111 * e112 * incl111to112;
    incl9to112 := Tensor(act, incl9to111, [id,u]) * incl111to112;
    proj112to9 := proj112to111 * Tensor(act, proj111to9, [id,u]);
    incl4to112 := Tensor(act, incl4to111, [id,u]) * incl111to112;
    proj112to4 := proj112to111 * Tensor(act, proj111to4, [id,u]);
    incl1to112 := Tensor(act, incl1to111, [id,u]) * incl111to112;
    proj112to1 := proj112to111 * Tensor(act, proj111to1, [id,u]);
    
    //e112 x 2 = e113 + e111
    f112_t := Tensor(act, e112red, [id,t]);
    br112to111 := (Braid(B,3,1) cat [2,1,2,1,4]) * ([3] cat Braid(B,2,1) cat [4]) * ([3,2,1,2,1] cat Braid(B,4,2));
    br111to112 := ([3,2,1,2,1] cat Braid(B,2,4)) * ([3] cat Braid(B,1,2) cat [4]) * (Braid(B,1,3) cat [2,1,2,1,4]);
    d112_111 := proj111to4 * Tensor(act, e4red, br112to111`stdmor * LocalisedLLDown(B,[1,3,2,1,2,1,4,3,2],[1,1,1,1,1,1,1,0,0])) * Tensor(act, incl4to112, BSId(B,2)`stdmor);
    u112_111 := Tensor(act, proj112to4, BSId(B,2)`stdmor) * Tensor(act, e4red, LocalisedLLUp(B,[1,3,2,1,2,1,4,3,2],[1,1,1,1,1,1,1,0,0]) * br111to112`stdmor) * incl4to111;
    b111_113 := d112_111 * u112_111;
    k111_113 := Matrix(b111_113)[1,1] / Matrix(e111red)[1,1];
    //k111_113 := -1;
    e113 := f112_t - 1/k111_113 * u112_111 * d112_111;
    proj113to112, incl112to113 := DecomposeIdem(e113);
    e113red := proj113to112 * e113 * incl112to113;
    incl9to113 := Tensor(act, incl9to112, [id,t]) * incl112to113;
    proj113to9 := proj113to112 * Tensor(act, proj112to9, [id,t]);
    incl1to113 := Tensor(act, incl1to112, [id,t]) * incl112to113;
    proj113to1 := proj113to112 * Tensor(act, proj112to1, [id,t]);
    
    //e113 x 1 = e114 + e112
    f113_s := Tensor(act, e113red, [id,s]);
    br113to112 := (Braid(B,4,1) cat [3]) * ([4] cat Braid(B,3,1));
    br112to113 := ([4] cat Braid(B,1,3)) * (Braid(B,1,4) cat [3]);
    d113_112 := proj112to9 * Tensor(act, e9red, br113to112`stdmor * LocalisedLLDown(B,[1,4,3,2,1],[1,1,1,0,0])) * Tensor(act, incl9to113, BSId(B,1)`stdmor);
    u113_112 := Tensor(act, proj113to9, BSId(B,1)`stdmor) * Tensor(act, e9red, LocalisedLLUp(B,[1,4,3,2,1],[1,1,1,0,0]) * br112to113`stdmor) * incl9to112;
    b112_114 := d113_112 * u113_112;
    k112_114 := Matrix(b112_114)[1,1] / Matrix(e112red)[1,1];
    //k112_114 := -f.1;
    e114 := f113_s - 1/k112_114 * u113_112 * d113_112;
    proj114to113, incl113to114 := DecomposeIdem(e114);
    e114red := proj114to113 * e114 * incl113to114;
    incl1to114 := Tensor(act, incl1to113, [id,s]) * incl113to114;
    proj114to1 := proj114to113 * Tensor(act, proj113to1, [id,s]);
    incl112to114 := Tensor(act, incl112to113, [id,s]) * incl113to114;
    proj114to112 := proj114to113 * Tensor(act, proj113to112, [id,s]);
    
    //e114 x 2 = e115 + e113
    f114_t := Tensor(act, e114red, [id,t]);
    d114_113 := proj113to112 * Tensor(act, e112red, LocalisedLLDown(B,[2,1,2],[1,0,0])) * Tensor(act, incl112to114, BSId(B,2)`stdmor);
    u114_113 := Tensor(act, proj114to112, BSId(B,2)`stdmor) * Tensor(act, e112red, LocalisedLLUp(B,[2,1,2],[1,0,0])) * incl112to113;
    b113_115 := d114_113 * u114_113;
    k113_115 := Matrix(b113_115)[1,1] / Matrix(e113red)[1,1];
    //k113_115 := -1;
    e115 := f114_t - 1/k113_115 * u114_113 * d114_113;
    proj115to114, incl114to115 := DecomposeIdem(e115);
    e115red := proj115to114 * e115 * incl114to115;   
    incl1to115 := Tensor(act, incl1to114, [id,t]) * incl114to115;
    proj115to1 := proj115to114 * Tensor(act, proj114to1, [id,t]);
    incl113to115 := Tensor(act, incl113to114, [id,t]) * incl114to115;
    proj115to113 := proj115to114 * Tensor(act, proj114to113, [id,t]);
    
    Sprintf("Idempotent 115 computed");  
    
    //e115 x 1 = e116 + e114 + e12 + e10
    //Longest calculation with 3 terms
    f115_s := Tensor(act, e115red, [id,s]);
    d115_114 := proj114to113 * Tensor(act, e113red, LocalisedLLDown(B,[1,2,1],[1,0,0])) * Tensor(act, incl113to115, BSId(B,1)`stdmor);
    u115_114 := Tensor(act, proj115to113, BSId(B,1)`stdmor) * Tensor(act, e113red, LocalisedLLUp(B,[1,2,1],[1,0,0])) * incl113to114;
    b114_116 := d115_114 * u115_114;
    k114_116 := Matrix(b114_116)[1,1] / Matrix(e114red)[1,1];
    //k114_116 := -f.1+1;
    
    br115to14 := (Braid(B,2,1) cat [3,2,1,2,1,3,2,1,2]) * ([2,1,2,1] cat Braid(B,3,2) cat [1,2,1,3,2,1,2]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2] cat Braid(B,3,1) cat [2,1,2]) * ([2,1,2,1,3,2,1] cat Braid(B,2,3) cat [1,2,1,2]) * ([2,1,2,1,3,2,1,2,3] cat Braid(B,1,2));
    br14to115 := ([2,1,2,1,3,2,1,2,3] cat Braid(B,2,1)) * ([2,1,2,1,3,2,1] cat Braid(B,3,2) cat [1,2,1,2]) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2] cat Braid(B,1,3) cat [2,1,2]) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2,1,3,2,1,2]) * (Braid(B,1,2) cat [3,2,1,2,1,3,2,1,2]);
    d115_14 := proj14to1 * br115to14`stdmor * LocalisedLLDown(B,[1,2,1,2,1,3,2,1,2,1,4,3,2,1,2,1],[1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,0]) * Tensor(act, incl1to115, BSId(B,1)`stdmor);
    u115_14 := Tensor(act, proj115to1, BSId(B,1)`stdmor) * LocalisedLLUp(B,[1,2,1,2,1,3,2,1,2,1,4,3,2,1,2,1],[1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,0]) * br14to115`stdmor * incl1to14;
    b14_116 := d115_14 * u115_14;
    k14_116 := Matrix(b14_116)[1,1] / Matrix(e14red)[1,1]; 
    //k14_116 := -1;
    
    br115to10 := ([1,2,1,2] cat Braid(B,3,1) cat [2,1,2,1]);
    br10to115 := ([1,2,1,2] cat Braid(B,1,3) cat [2,1,2,1]);
    d115_10 := proj10to1 * br115to10`stdmor * LocalisedLLDown(B,[1,2,1,2,1,3,2,1,2,1,4,3,2,1,2,1],[1,1,1,1,0,1,0,1,1,1,0,0,1,1,0,0]) * Tensor(act, incl1to115, BSId(B,1)`stdmor);
    u115_10 := Tensor(act, proj115to1, BSId(B,1)`stdmor) * LocalisedLLUp(B,[1,2,1,2,1,3,2,1,2,1,4,3,2,1,2,1],[1,1,1,1,0,1,0,1,1,1,0,0,1,1,0,0]) * br10to115`stdmor * incl1to10;
    b10_116 := d115_10 * u115_10;
    k10_116 := Matrix(b10_116)[1,1] / Matrix(e10red)[1,1]; 
    //k10_116 := -1;
    
    e116 := f115_s - 1/k114_116 * u115_114 * d115_114 - 1/k14_116 * u115_14 * d115_14 - 1/k10_116 * u115_10 * d115_10 ;
    proj116to115, incl115to116 := DecomposeIdem(e116);
    e116red := proj116to115 * e116 * incl115to116;   
    
    Sprintf("All idempotents computed; now their mirror image");  

    //eflip1
    eflip1 := BSId(B,1)`stdmor;

    //eflip2
    eflip2 := Tensor(act, [id,t], eflip1);
    projflip2to1, inclflip1to2 := DecomposeIdem(eflip2);

    //eflip3
    fflips_2 := Tensor(act, [id,s], eflip2);
    dflip2_1 := eflip1 * LocalisedLLDown(B,[1,2,1],[1,0,0]) * fflips_2;
    uflip2_1 := fflips_2 * LocalisedLLUp(B,[1,2,1],[1,0,0]) * eflip1;
    //bflip1_3 := dflip2_1 * uflip2_1;
    //kflip1_3 := Matrix(bflip1_3)[1,1] / Matrix(eflip1)[1,1];
    kflip1_3 := -f.1;
    eflip3 := fflips_2 - 1/kflip1_3 * uflip2_1 * dflip2_1;
    projflip3to1, inclflip1to3 := DecomposeIdem(eflip3);
    eflip3red := projflip3to1 * eflip3 * inclflip1to3;

    //eflip4
    fflipt_3 := Tensor(act, [id,t], eflip3red);
    inclflip3_t := Tensor(act, [id,t], inclflip1to3);
    projflip3_t := Tensor(act, [id,t], projflip3to1);
    dflip3_2 := eflip2 * LocalisedLLDown(B,[2,1,2,1],[1,0,0,1]) * inclflip3_t * fflipt_3;
    uflip3_2 := fflipt_3 * projflip3_t * LocalisedLLUp(B,[2,1,2,1],[1,0,0,1]) * eflip2;
    //bflip2_4 := dflip3_2 * uflip3_2;
    //kflip2_4 := Matrix(bflip2_4)[1,1] / Matrix(eflip2)[1,1];
    kflip2_4 := -1;
    eflip4 := fflipt_3 - 1/kflip2_4 * uflip3_2 * dflip3_2;
    projflip4to3, inclflip3to4 := DecomposeIdem(eflip4);
    eflip4red := projflip4to3 * eflip4 * inclflip3to4;
    inclflip1to4 := Tensor(act, [id,t], inclflip1to3) * inclflip3to4;
    projflip4to1 := projflip4to3 * Tensor(act, [id,t], projflip3to1);

    //eflip5
    fflips_4 := Tensor(act, [id,s], eflip4red);
    dflip4_3 := eflip3red * projflip3to1 * (Tensor(act, LocalisedLLDown(B,[1,2,1],[1,0,0]), eflip2)) * Tensor(act, [id,s], inclflip1to4) * fflips_4;
    uflip4_3 := fflips_4 * Tensor(act, [id,s], projflip4to1) * Tensor(act, LocalisedLLUp(B,[1,2,1],[1,0,0]), eflip2) * inclflip1to3 * eflip3red;
    //bflip3_5 := dflip4_3 * uflip4_3;
    //kflip3_5 := Matrix(bflip3_5)[1,1] / Matrix(eflip3red)[1,1];
    kflip3_5 := -f.1 +1;
    eflip5 := fflips_4 - 1/kflip3_5 * uflip4_3 * eflip3red * dflip4_3;
    projflip5to4, inclflip4to5 := DecomposeIdem(eflip5);
    eflip5red := projflip5to4 * eflip5 * inclflip4to5;
    inclflip1to5 := Tensor(act, [id,s], inclflip1to4) * inclflip4to5;
    projflip5to1 := projflip5to4 * Tensor(act, [id,s], projflip4to1);
    inclflip3to5 := Tensor(act, [id,s], inclflip3to4) * inclflip4to5;
    projflip5to3 := projflip5to4 * Tensor(act, [id,s], projflip4to3);

    //eflip6
    eflip6 := Tensor(act, [id,u], eflip5red);
    projflip6to5, inclflip5to6 := DecomposeIdem(eflip6);
    eflip6red := projflip6to5 * eflip6 * inclflip5to6;
    inclflip1to6 := Tensor(act, [id,u], inclflip1to5) * inclflip5to6;
    projflip6to1 := projflip6to5 * Tensor(act, [id,u], projflip5to1);
    inclflip4to6 := Tensor(act, [id,u], inclflip4to5) * inclflip5to6;
    projflip6to4 := projflip6to5 * Tensor(act, [id,u], projflip5to4);

    //From here on out we need braids:
    fflipt_6 := Tensor(act, [id,t], eflip6red);
    brflip6to5 := ([2,3] cat Braid(B,1,2))`stdmor;
    brflip5from6 := (Braid(B,2,1))`stdmor;
    brflip5to6 := (Braid(B,1,2))`stdmor;
    brflip6from5 := ([2,3] cat Braid(B,2,1))`stdmor;

    dflip6_5 := eflip5red * projflip5to1 * brflip5from6 * LocalisedLLDown(B,[2,3,2,1,2,1,2],[1,0,0,1,1,1,1]) * brflip6to5 * Tensor(act, [id,t], inclflip1to6) * fflipt_6;
    uflip6_5 := fflipt_6 * Tensor(act, [id,t], projflip6to1) * brflip6from5 * LocalisedLLUp(B,[2,3,2,1,2,1,2],[1,0,0,1,1,1,1]) * brflip5to6 * inclflip1to5 * eflip5red;

    //bflip5_7 := dflip6_5 * uflip6_5;
    //kflip5_7 := Matrix(bflip5_7)[1,1] / Matrix(eflip5red)[1,1];
    kflip5_7 := -1;
    eflip7 := fflipt_6 - 1/kflip5_7 * uflip6_5 * dflip6_5;
    projflip7to6, inclflip6to7 := DecomposeIdem(eflip7);
    eflip7red := projflip7to6 * eflip7 * inclflip6to7;
    inclflip1to7 := Tensor(act, [id,t], inclflip1to6) * inclflip6to7;
    projflip7to1 := projflip7to6 * Tensor(act, [id,t], projflip6to1);
    inclflip5to7 := Tensor(act, [id,t], inclflip5to6) * inclflip6to7;
    projflip7to5 := projflip7to6 * Tensor(act, [id,t], projflip6to5);
    inclflip4to7 := Tensor(act, [id,t], inclflip4to6) * inclflip6to7;
    projflip7to4 := projflip7to6 * Tensor(act, [id,t], projflip6to4);

    //eflip8:
    fflips_7 := Tensor(act, [id,s], eflip7red);
    //We include e7red into e4\otimes 132 so that we can braid in the end; then tensor with s, apply light leave, braid back and project back onto e7red
    dflip7_6 := projflip6to4 * Tensor(act, Braid(B,1,3)`stdmor, eflip4red) * Tensor(act, LocalisedLLDown(B,[1,2,1,3],[1,0,0,1]), eflip4red) * Tensor(act ,[id,s], Tensor(act, [id,t], Tensor(act, Braid(B,3,1)`stdmor, eflip4red)) * inclflip4to7) * fflips_7;                     
    uflip7_6 := fflips_7 * Tensor(act ,[id,s], projflip7to4 * Tensor(act, [id,t], Tensor(act, Braid(B,1,3)`stdmor, eflip4red))) * Tensor(act, LocalisedLLUp(B,[1,2,1,3],[1,0,0,1]), eflip4red) * Tensor(act, Braid(B,3,1)`stdmor, eflip4red) * inclflip4to6;
    //bflip6_8 := dflip7_6 * uflip7_6;
    //kflip6_8 := Matrix(bflip6_8)[1,1] / Matrix(eflip6red)[1,1];
    kflip6_8 := -f.1;
    eflip8 := fflips_7 - 1/kflip6_8 * uflip7_6 * dflip7_6;
    projflip8to7, inclflip7to8 := DecomposeIdem(eflip8);
    eflip8red := projflip8to7 * eflip8 * inclflip7to8;
    inclflip6to8 := Tensor(act, [id,s], inclflip6to7) * inclflip7to8;
    projflip8to6 := projflip8to7 * Tensor(act, [id,s], projflip7to6);
    inclflip1to8 := Tensor(act, [id,s], inclflip1to7) * inclflip7to8;
    projflip8to1 := projflip8to7 * Tensor(act, [id,s], projflip7to1);
    inclflip5to8 := Tensor(act, [id,s], inclflip5to7) * inclflip7to8;
    projflip8to5 := projflip8to7 * Tensor(act, [id,s], projflip7to5);
    inclflip4to8 := Tensor(act, [id,s], inclflip4to7) * inclflip7to8;
    projflip8to4 := projflip8to7 * Tensor(act, [id,s], projflip7to4);

    //eflip9:
    fflipt_8 := Tensor(act, [id,t], eflip8red);
    dflip8_7 := projflip7to6 * Tensor(act, LocalisedLLDown(B,[2,1,2],[1,0,0]), eflip6red) * Tensor(act, [id,t], inclflip6to8);
    uflip8_7 := Tensor(act, [id,t], projflip8to6) * Tensor(act, LocalisedLLUp(B,[2,1,2],[1,0,0]), eflip6red) * inclflip6to7;
    bflip7_9 := dflip8_7 * uflip8_7;
    kflip7_9 := Matrix(bflip7_9)[1,1] / Matrix(eflip7red)[1,1];
    //k7_9 := -1; 
    eflip9 := Tensor(act, [id,t], eflip8red) - 1/kflip7_9 * uflip8_7 * dflip8_7;
    projflip9to8, inclflip8to9 := DecomposeIdem(eflip9);
    eflip9red := projflip9to8 * eflip9 * inclflip8to9;
    inclflip7to9 := Tensor(act, [id,t], inclflip7to8) * inclflip8to9;
    projflip9to7 := projflip9to8 * Tensor(act, [id,t], projflip8to7);
    inclflip1to9 := Tensor(act, [id,t], inclflip1to8) * inclflip8to9;
    projflip9to1 := projflip9to8 * Tensor(act, [id,t], projflip8to1);
    inclflip5to9 := Tensor(act, [id,t], inclflip5to8) * inclflip8to9;
    projflip9to5 := projflip9to8 * Tensor(act, [id,t], projflip8to5);
    inclflip4to9 := Tensor(act, [id,t], inclflip4to8) * inclflip8to9;
    projflip9to4 := projflip9to8 * Tensor(act, [id,t], projflip8to4);
    
    //eflip10
    fflips_9 := Tensor(act, [id,s], eflip9red);
    dflip9_8 := projflip8to7 * Tensor(act, LocalisedLLDown(B,[1,2,1],[1,0,0]), eflip7red) * Tensor(act, [id,s], inclflip7to9);
    uflip9_8 := Tensor(act, [id,s], projflip9to7) * Tensor(act, LocalisedLLUp(B,[1,2,1],[1,0,0]), eflip7red) * inclflip7to8;
    //bflip8_10 := dflip9_8 * uflip9_8;
    //kflip8_10 := Matrix(bflip8_10)[1,1] / Matrix(eflip8red)[1,1];
    kflip8_10 := -f.1+1;
    eflip10 := Tensor(act, [id,s], eflip9red) - 1/kflip8_10 * uflip9_8 * dflip9_8;
    projflip10to9, inclflip9to10 := DecomposeIdem(eflip10);
    eflip10red := projflip10to9 * eflip10 * inclflip9to10;
    inclflip5to10 := Tensor(act, [id,s], inclflip5to9) * inclflip9to10;
    projflip10to5 := projflip10to9 * Tensor(act, [id,s], projflip9to5);
    inclflip1to10 := Tensor(act, [id,s], inclflip1to9) * inclflip9to10;
    projflip10to1 := projflip10to9 * Tensor(act, [id,s], projflip9to1);
    inclflip4to10 := Tensor(act, [id,s], inclflip4to9) * inclflip9to10;
    projflip10to4 := projflip10to9 * Tensor(act, [id,s], projflip9to4);
    
    //eflipx
    dflipx_8 := projflip8to1  * LocalisedLLDown(B,[3,2,1,2,3,1,2,1,2,1],[1,0,1,1,1,1,1,1,1,0]) * Tensor(act, [id,u], inclflip1to9);
    uflipx_8 := Tensor(act, [id,u], projflip9to1) * LocalisedLLUp(B,[3,2,1,2,3,1,2,1,2,1],[1,0,1,1,1,1,1,1,1,0]) * inclflip1to8;
    kflip8_x := -1;
    
    eflipx := Tensor(act, [id, u], eflip9red) - 1/kflip8_x * uflipx_8 * dflipx_8;
    projflipxto9, inclflip9tox := DecomposeIdem(eflipx);
    eflipxred := projflipxto9 * eflipx * inclflip9tox;
    inclflip1tox := Tensor(act, [id,u], inclflip1to9) * inclflip9tox;
    projflipxto1 := projflipxto9 * Tensor(act, [id,u], projflip9to1);

    //eflip11:
    eflip11 := Tensor(act, [id,u], eflip10red);
    projflip11to10, inclflip10to11 := DecomposeIdem(eflip11);
    eflip11red := projflip11to10 * eflip11 * inclflip10to11;
    inclflip9to11 := Tensor(act, [id,u], inclflip9to10) * inclflip10to11;
    projflip11to9 := projflip11to10 * Tensor(act, [id,u], projflip10to9);
    inclflip5to11 := Tensor(act, [id,u], inclflip5to10) * inclflip10to11;
    projflip11to5 := projflip11to10 * Tensor(act, [id,u], projflip10to5);
    inclflip4to11 := Tensor(act, [id,u], inclflip4to10) * inclflip10to11;
    projflip11to4 := projflip11to10 * Tensor(act, [id,u], projflip10to4);
    inclflip1to11 := Tensor(act, [id,u], inclflip1to10) * inclflip10to11;
    projflip11to1 := projflip11to10 * Tensor(act, [id,u], projflip10to1);

    //eflip12:
    dflip11_10 := projflip10to4 * Tensor(act, LocalisedLLDown(B,[2,3,1,2,1,2,3,1],[1,0,1,1,1,1,1,0]), eflip4red) * Tensor(act, [id,t], inclflip4to11);
    uflip11_10 := Tensor(act, [id,t], projflip11to4) * Tensor(act, LocalisedLLUp(B,[2,3,1,2,1,2,3,1],[1,0,1,1,1,1,1,0]), eflip4red) * inclflip4to10;
    kflip10_12 := -1;

    dflip11_x := projflipxto1 * LocalisedLLDown(B,[2,3,1,2,1,2,3,1,2,1,2,1],[1,1,0,1,1,1,1,1,1,1,1,0]) * Tensor(act, [id,t], inclflip1to11);
    uflip11_x := Tensor(act, [id,t], projflip11to1) * LocalisedLLUp(B,[2,3,1,2,1,2,3,1,2,1,2,1],[1,1,0,1,1,1,1,1,1,1,1,0]) * inclflip1tox;
    kflipx_12 := -f.1;

    eflip12 := Tensor(act, [id,t], eflip11red) - 1/kflip10_12 * uflip11_10 * dflip11_10 - 1/kflipx_12 * uflip11_x * dflip11_x;
    projflip12to11, inclflip11to12 := DecomposeIdem(eflip12);
    eflip12red := projflip12to11 * eflip12 * inclflip11to12;
    inclflip10to12 := Tensor(act, [id,t], inclflip10to11) * inclflip11to12;
    projflip12to10 := projflip12to11 * Tensor(act, [id,t], projflip11to10);
    inclflip9to12 := Tensor(act, [id,t], inclflip9to11) * inclflip11to12;
    projflip12to9 := projflip12to11 * Tensor(act, [id,t], projflip11to9);
    inclflip1to12 := Tensor(act, [id,t], inclflip1to11) * inclflip11to12;
    projflip12to1 := projflip12to11 * Tensor(act, [id,t], projflip11to1);

    //eflip13
    dflip12_11 := projflip11to9 * Tensor(act, LocalisedLLDown(B,[1,2,3,1],[1,0,1,0]), eflip9red) * Tensor(act, [id,s], inclflip9to12);
    uflip12_11 := Tensor(act, [id,s], projflip12to9) * Tensor(act, LocalisedLLUp(B,[1,2,3,1],[1,0,1,0]), eflip9red) * inclflip9to11;
    kflip11_13 := -1;

    eflip13 := Tensor(act, [id,s], eflip12red) - 1/kflip11_13 * uflip12_11 * dflip12_11;
    projflip13to12, inclflip12to13 := DecomposeIdem(eflip13);
    eflip13red := projflip13to12 * eflip13 * inclflip12to13;
    inclflip11to13 := Tensor(act, [id,s], inclflip11to12) * inclflip12to13;
    projflip13to11 := projflip13to12 * Tensor(act, [id,s], projflip12to11);
    inclflip1to13 := Tensor(act, [id,s], inclflip1to12) * inclflip12to13;
    projflip13to1 := projflip13to12 * Tensor(act, [id,s], projflip12to1);
    inclflip9to13 := Tensor(act, [id,s], inclflip9to12) * inclflip12to13;
    projflip13to9 := projflip13to12 * Tensor(act, [id,s], projflip12to9);

    //eflip14
    dflip13_12 := projflip12to11 * Tensor(act, LocalisedLLDown(B,[2,1,2],[1,0,0]), eflip11red) * Tensor(act, [id,t], inclflip11to13);
    uflip13_12 := Tensor(act, [id,t], projflip13to11) * Tensor(act, LocalisedLLUp(B,[2,1,2],[1,0,0]), eflip11red) * inclflip11to12;
    kflip12_14 := -f.1 + 1;
    
    eflip14 := Tensor(act, [id,t], eflip13red) - 1/kflip12_14 * uflip13_12 * dflip13_12;
    projflip14to13, inclflip13to14 := DecomposeIdem(eflip14);
    eflip14red := projflip14to13 * eflip14 * inclflip13to14;
    inclflip1to14 := Tensor(act, [id,t], inclflip1to13) * inclflip13to14;
    projflip14to1 := projflip14to13 * Tensor(act, [id,t], projflip13to1);
    inclflip9to14 := Tensor(act, [id,t], inclflip9to13) * inclflip13to14;
    projflip14to9 := projflip14to13 * Tensor(act, [id,t], projflip13to9);
    
    //eflip111
    eflip111 := Tensor(act,[id,v], eflip10red);
    projflip111to10, inclflip10to111 := DecomposeIdem(eflip111);
    eflip111red := projflip111to10 * eflip111 * inclflip10to111;
    inclflip9to111 := Tensor(act, [id,v], inclflip9to10) * inclflip10to111;
    projflip111to9 := projflip111to10 * Tensor(act, [id,v], projflip10to9);
    inclflip4to111 := Tensor(act, [id,v], inclflip4to10) * inclflip10to111;
    projflip111to4 := projflip111to10 * Tensor(act, [id,v], projflip10to4);
    inclflip1to111 := Tensor(act, [id,v], inclflip1to10) * inclflip10to111;
    projflip111to1 := projflip111to10 * Tensor(act, [id,v], projflip10to1);
    
    //eflip112
    eflip112 := Tensor(act, [id,u], eflip111red);
    projflip112to111, inclflip111to112 := DecomposeIdem(eflip112);
    eflip112red := projflip112to111 * eflip112 * inclflip111to112;
    inclflip9to112 := Tensor(act, [id,u], inclflip9to111) * inclflip111to112;
    projflip112to9 := projflip112to111 * Tensor(act, [id,u], projflip111to9);
    inclflip4to112 := Tensor(act, [id,u], inclflip4to111) * inclflip111to112;
    projflip112to4 := projflip112to111 * Tensor(act, [id,u], projflip111to4);
    inclflip1to112 := Tensor(act, [id,u], inclflip1to111) * inclflip111to112;
    projflip112to1 := projflip112to111 * Tensor(act, [id,u], projflip111to1);
    
    //eflip113
    fflip112_t := Tensor(act, [id,t], eflip112red);
    dflip112_111 := projflip111to4 * Tensor(act, LocalisedLLDown(B,[2,3,4,1,2,1,2,3,1],[1,0,1,1,1,1,1,1,0]), eflip4red) * Tensor(act, BSId(B,2)`stdmor, inclflip4to112);
    uflip112_111 := Tensor(act, BSId(B,2)`stdmor, projflip112to4) * Tensor(act, LocalisedLLUp(B,[2,3,4,1,2,1,2,3,1],[1,0,1,1,1,1,1,1,0]), eflip4red) * inclflip4to111;
    //bflip111_113 := dflip112_111 * uflip112_111;
    //kflip111_113 := Matrix(bflip111_113)[1,1] / Matrix(eflip111red)[1,1];
    kflip111_113 := -1;
    eflip113 := fflip112_t - 1/kflip111_113 * uflip112_111 * dflip112_111;
    projflip113to112, inclflip112to113 := DecomposeIdem(eflip113);
    eflip113red := projflip113to112 * eflip113 * inclflip112to113;
    inclflip9to113 := Tensor(act, [id,t], inclflip9to112) * inclflip112to113;
    projflip113to9 := projflip113to112 * Tensor(act, [id,t], projflip112to9);
    inclflip1to113 := Tensor(act, [id,t], inclflip1to112) * inclflip112to113;
    projflip113to1 := projflip113to112 * Tensor(act, [id,t], projflip112to1);
    inclflip4to113 := Tensor(act, [id,t], inclflip4to112) * inclflip112to113;
    projflip113to4 := projflip113to112 * Tensor(act, [id,t], projflip112to4);
    
    //eflip114
    fflip113_s := Tensor(act, [id,s], eflip113red);
    dflip113_112 := projflip112to9 * Tensor(act, LocalisedLLDown(B,[1,2,3,4,1],[1,0,1,1,0]), eflip9red) * Tensor(act, BSId(B,1)`stdmor, inclflip9to113);
    uflip113_112 := Tensor(act, BSId(B,1)`stdmor, projflip113to9) * Tensor(act, LocalisedLLUp(B,[1,2,3,4,1],[1,0,1,1,0]), eflip9red) * inclflip9to112;
    //bflip112_114 := dflip113_112 * uflip113_112;
    //kflip112_114 := Matrix(bflip112_114)[1,1] / Matrix(eflip112red)[1,1];
    kflip112_114 := -f.1;
    eflip114 := fflip113_s - 1/kflip112_114 * uflip113_112 * dflip113_112;
    projflip114to113, inclflip113to114 := DecomposeIdem(eflip114);
    eflip114red := projflip114to113 * eflip114 * inclflip113to114;
    inclflip1to114 := Tensor(act, [id,s], inclflip1to113) * inclflip113to114;
    projflip114to1 := projflip114to113 * Tensor(act, [id,s], projflip113to1);
    inclflip112to114 := Tensor(act, [id,s], inclflip112to113) * inclflip113to114;
    projflip114to112 := projflip114to113 * Tensor(act, [id,s], projflip113to112);
    inclflip9to114 := Tensor(act, [id,s], inclflip9to113) * inclflip113to114;
    projflip114to9 := projflip114to113 * Tensor(act, [id,s], projflip113to9);
    inclflip4to114 := Tensor(act, [id,s], inclflip4to113) * inclflip113to114;
    projflip114to4 := projflip114to113 * Tensor(act, [id,s], projflip113to4);
    
    //eflip115
    fflip114_t := Tensor(act, [id,t], eflip114red);
    dflip114_113 := projflip113to112 * Tensor(act, LocalisedLLDown(B,[2,1,2],[1,0,0]), eflip112red) * Tensor(act, BSId(B,2)`stdmor, inclflip112to114);
    uflip114_113 := Tensor(act, BSId(B,2)`stdmor, projflip114to112) * Tensor(act, LocalisedLLUp(B,[2,1,2],[1,0,0]), eflip112red) * inclflip112to113;
    //b113_115 := d114_113 * u114_113;
    //k113_115 := Matrix(b113_115)[1,1] / Matrix(e113red)[1,1];
    kflip113_115 := -1;
    eflip115 := fflip114_t - 1/kflip113_115 * uflip114_113 * dflip114_113;
    projflip115to114, inclflip114to115 := DecomposeIdem(eflip115);
    eflip115red := projflip115to114 * eflip115 * inclflip114to115;   
    inclflip1to115 := Tensor(act, [id,t], inclflip1to114) * inclflip114to115;
    projflip115to1 := projflip115to114 * Tensor(act, [id,t], projflip114to1);
    inclflip113to115 := Tensor(act, [id,t], inclflip113to114) * inclflip114to115;
    projflip115to113 := projflip115to114 * Tensor(act, [id,t], projflip114to113);
    inclflip4to115 := Tensor(act, [id,t], inclflip4to114) * inclflip114to115;
    projflip115to4 := projflip115to114 * Tensor(act, [id,t], projflip114to4);
    
    //eflip116 
    //Longest calculation with 3 terms
    fflip115_s := Tensor(act, [id,s], eflip115red);
    dflip115_114 := projflip114to113 * Tensor(act, LocalisedLLDown(B,[1,2,1],[1,0,0]), eflip113red) * Tensor(act, BSId(B,1)`stdmor, inclflip113to115);
    uflip115_114 := Tensor(act, BSId(B,1)`stdmor, projflip115to113) * Tensor(act, LocalisedLLUp(B,[1,2,1],[1,0,0]), eflip113red) * inclflip113to114;
    kflip114_116 := -f.1+1;
    
    brflip115to14 := ([2,1,2] cat Braid(B,1,3));
    brflip14to115 := ([2,1,2] cat Braid(B,3,1));
    dflip115_14 := projflip14to9 * Tensor(act, brflip115to14`stdmor, projflip9to1) * LocalisedLLDown(B,[1,2,1,2,3,4,1,2,1,2,3,1,2,1,2,1],[1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,0]) * Tensor(act, BSId(B,1)`stdmor, inclflip1to115);
    uflip115_14 := Tensor(act, BSId(B,1)`stdmor, projflip115to1) * LocalisedLLUp(B,[1,2,1,2,3,4,1,2,1,2,3,1,2,1,2,1],[1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,0]) * Tensor(act, brflip14to115`stdmor, inclflip1to9) * inclflip9to14;
    kflip14_116 := -1;
    
    //Maybe it is 1111100011011100
    dflip115_10 := projflip10to1 * LocalisedLLDown(B,[1,2,1,2,3,4,1,2,1,2,3,1,2,1,2,1],[1,1,1,1,1,0,0,0,1,1,0,1,1,1,0,0]) * Tensor(act, BSId(B,1)`stdmor, inclflip1to115);
    uflip115_10 := Tensor(act, BSId(B,1)`stdmor, projflip115to1) * LocalisedLLUp(B,[1,2,1,2,3,4,1,2,1,2,3,1,2,1,2,1],[1,1,1,1,1,0,0,0,1,1,0,1,1,1,0,0]) * inclflip1to10;
    kflip10_116 := -1;
    
    eflip116 := fflip115_s - 1/kflip114_116 * uflip115_114 * dflip115_114 - 1/kflip14_116 * uflip115_14 * dflip115_14 - 1/kflip10_116 * uflip115_10 * dflip115_10;
    projflip116to115, inclflip115to116 := DecomposeIdem(eflip116);
    eflip116red := projflip116to115 * eflip116 * inclflip115to116;   

	Sprintf("All idempotents computed");    

    //The goal is to construct the maps e14 -> e10 x eflip10 -> e14 as in the document

    //Top maps; we simplify them step by step
    t1 := Tensor(act, proj10to9, eflip9red) * Tensor(act, e9red, Tensor(act, Mult(B,1)`stdmor, eflip9red)) * Tensor(act, incl9to10, inclflip9to10);
    b1 := Tensor(act, proj10to9, projflip10to9) * Tensor(act, e9red, Tensor(act, Comult(B,1)`stdmor, eflip9red)) * Tensor(act, incl9to10, eflip9red);

    //Construct extra help maps for second step. Here we need to go a step back as we need to apply a braid
    top2map1 := ((Braid(B,3,1) cat [2,1,2,1]) * ([3] cat Braid(B,2,1)) * ([3,2,1,2,1] cat Mult(B,2)) * ([3] cat Braid(B,1,2) cat [2]) * (Braid(B,1,3) cat [2,1,2,1,2]))`stdmor; 
    top2map2 := proj10to4 * Tensor(act, e4red, top2map1) * Tensor(act, incl4to10, BSId(B,2)`stdmor);
    top2map3 := Tensor(act, e10red, eflip8red) * Tensor(act, top2map2, eflip8red) * Tensor(act, e10red, inclflip8to9);

    bot2map1 := ((Braid(B,3,1) cat [2,1,2,1,2]) * ([3] cat Braid(B,2,1) cat [2]) * ([3,2,1,2,1] cat Comult(B,2)) * ([3] cat Braid(B,1,2)) * (Braid(B,1,3) cat [2,1,2,1]))`stdmor; 
    bot2map2 := Tensor(act, proj10to4, BSId(B,2)`stdmor) * Tensor(act, e4red, bot2map1) * incl4to10;
    bot2map3 := Tensor(act, e10red, projflip9to8) * Tensor(act, bot2map2, eflip8red) * Tensor(act, e10red, eflip8red);

    t2 := top2map3 * t1;
    b2 := b1 * bot2map3;

    //No braid needed; we are now at : 1212132121 \otimes 12312121	
    top3map1 := proj10to9 * Tensor(act, e9red, Mult(B,1)`stdmor) * Tensor(act, incl9to10, BSId(B,1)`stdmor);
    top3map2 := Tensor(act, e10red, eflip7red) * Tensor(act, top3map1, eflip7red) * Tensor(act, e10red, inclflip7to8);

    bot3map1 := Tensor(act, proj10to9, BSId(B,1)`stdmor) * Tensor(act, e9red, Comult(B,1)`stdmor) * incl9to10;
    bot3map2 := Tensor(act, e10red, projflip8to7) * Tensor(act, bot3map1, eflip7red) * Tensor(act, e10red, eflip7red);

    t3 := top3map2 * t2;
    b3 := b2 * bot3map2;

    //Other braiding step for 1212132121 \otimes 2312121
    top4map1 := ((Braid(B,3,1) cat [2,1,2,1]) * ([3] cat Braid(B,2,1)) * ([3,2,1,2,1] cat Mult(B,2)) * ([3] cat Braid(B,1,2) cat [2]) * (Braid(B,1,3) cat [2,1,2,1,2]))`stdmor; 
    top4map2 := proj10to4 * Tensor(act, e4red, top2map1) * Tensor(act, incl4to10, BSId(B,2)`stdmor);
    top4map3 := Tensor(act, e10red, eflip6red) * Tensor(act, top2map2, eflip6red) * Tensor(act, e10red, inclflip6to7);

    bot4map1 := ((Braid(B,3,1) cat [2,1,2,1,2]) * ([3] cat Braid(B,2,1) cat [2]) * ([3,2,1,2,1] cat Comult(B,2)) * ([3] cat Braid(B,1,2)) * (Braid(B,1,3) cat [2,1,2,1]))`stdmor; 
    bot4map2 := Tensor(act, proj10to4, BSId(B,2)`stdmor) * Tensor(act, e4red, bot2map1) * incl4to10;
    bot4map3 := Tensor(act, e10red, projflip7to6) * Tensor(act, bot2map2, eflip6red) * Tensor(act, e10red, eflip6red);

    t4 := top4map3 * t3;
    b4 := b3 * bot4map3;

    //For next reduction need one more braid on right side for (1,3): 1212132121 \otimes 312121
    top5map1 := proj10to9 * Tensor(act, e9red, Mult(B,1)`stdmor) * Tensor(act, incl9to10, BSId(B,1)`stdmor);
    top5map2 := Tensor(act, e10red, Tensor(act, BSId(B,3)`stdmor, eflip4red)) * Tensor(act, top5map1, Tensor(act, BSId(B,3)`stdmor, eflip4red)) * Tensor(act, e10red, Tensor(act, Braid(B,3,1)`stdmor, eflip4red)) * Tensor(act, e10red, inclflip4to6);

    bot5map1 := Tensor(act, proj10to9, BSId(B,1)`stdmor) * Tensor(act, e9red, Comult(B,1)`stdmor) * incl9to10;
    bot5map2 := Tensor(act, e10red, projflip6to4) * Tensor(act, e10red, Tensor(act, Braid(B,1,3)`stdmor, eflip4red)) * Tensor(act, bot5map1, Tensor(act, BSId(B,3)`stdmor, eflip4red)) * Tensor(act, e10red, Tensor(act, BSId(B,3)`stdmor, eflip4red));

    t5 := top5map2 * t4;
    b5 := b4 * bot5map2;

    //now we go from 10x5 to 11x4:
    top6map :=  Tensor(act, proj11to10, eflip4red);
    bot6map :=  Tensor(act, incl10to11, eflip4red); 

    t6 := top6map * t5;
    b6 := b5 * bot6map;

    //now we go from 11x4 to 12x3:
    top7map :=  Tensor(act, proj12to11, eflip3red) * Tensor(act, e11red, inclflip3to4); 
    bot7map :=  Tensor(act, e11red, projflip4to3) * Tensor(act, incl11to12, eflip3red); 

    t7 := top7map * t6;
    b7 := b6 * bot7map;

    //now we go from 12x3 to 13x2:
    top8map :=  Tensor(act, proj13to12, eflip2) * Tensor(act, e12red, inclflip1to3); 
    bot8map :=  Tensor(act, e12red, projflip3to1) * Tensor(act, incl12to13, eflip2); 

    t8 := top8map * t7;
    b8 := b7 * bot8map;

    //now we go from 13x2 to 14x1:
    top9map :=  Tensor(act, proj14to13, eflip1) * Tensor(act, e13red, inclflip1to2); 
    bot9map :=  Tensor(act, e13red, projflip2to1) * Tensor(act, incl13to14, eflip1); 

    t9 := top9map * t8;
    b9 := b8 * bot9map;

    //Final Step. Apply braidings and Use Mult:
    braid14 := (([2,1,2,1,3,2,1,2,3] cat Braid(B,2,1)) * ([2,1,2,1,3,2,1] cat Braid(B,3,2) cat [1,2,1,2]) * ([2,1,2,1,3,2] cat Braid(B,3,1) cat [2,3,1,2,1,2]) * ([2,1,2,1] cat Braid(B,2,3) cat [1,2] cat Braid(B,1,3) cat [2,1,2]) * (Braid(B,1,2) cat [3,2,1,2,1,3,2,1,2]))`stdmor;
    braid14back := ((Braid(B,2,1) cat [3,2,1,2,1,3,2,1,2]) * ([2,1,2,1] cat Braid(B,3,2) cat [1,2] cat Braid(B,3,1) cat [2,1,2]) * ([2,1,2,1,3,2] cat Braid(B,1,3) cat [2,3,1,2,1,2]) * ([2,1,2,1,3,2,1] cat Braid(B,2,3) cat [1,2,1,2]) * ([2,1,2,1,3,2,1,2,3] cat Braid(B,1,2)))`stdmor;

    top10map := proj14to1 * braid14back * Tensor(act, BSId(B,[2,1,2,1,3,2,1,2,3,1,2,1,2])`stdmor, Mult(B,1)`stdmor) * Tensor(act, braid14, eflip1) * Tensor(act, incl1to14, eflip1);
    bot10map := Tensor(act, proj14to1, eflip1) * Tensor(act, braid14back, eflip1) * Tensor(act, BSId(B,[2,1,2,1,3,2,1,2,3,1,2,1,2])`stdmor, Comult(B,1)`stdmor) * braid14 * incl1to14;

    t10:= top10map * t9;
    b10 := b9 * bot10map;

    //positive root:
    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
  
    //Then we can compute the dimension of e10
    middle := Tensor(act, e10red, root^6*eflip10red);
    
    trace10 := t10 * middle * b10;
    dim10 := trace10`mat[1,1]/trace10`mat[1,1];
    
    T1 := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("The dimension of ed is %o. Total time for the calculation 	took %o, used space was %o.", dim10, T1, S);
    
    //Maps for e116 x eflip116 to e10 x dflip10
    partial10top := t10*Tensor(act, e10red, Tensor(act, Cap(B,4)`stdmor, eflip10red)) * Tensor(act, incl10to111, inclflip10to111);
    partial111top := partial10top * Tensor(act, e111red, Tensor(act, Cap(B,3)`stdmor, eflip111red)) * Tensor(act, incl111to112, inclflip111to112);
    partial112top := partial111top * Tensor(act, e112red, Tensor(act, Cap(B,2)`stdmor, eflip112red)) * Tensor(act, incl112to113, inclflip112to113);
    partial113top := partial112top * Tensor(act, e113red, Tensor(act, Cap(B,1)`stdmor, eflip113red)) * Tensor(act, incl113to114, inclflip113to114);
    partial114top := partial113top * Tensor(act, e114red, Tensor(act, Cap(B,2)`stdmor, eflip114red)) * Tensor(act, incl114to115, inclflip114to115);
    partial115top := partial114top * Tensor(act, e115red, Tensor(act, Cap(B,1)`stdmor, eflip115red)) * Tensor(act, incl115to116, inclflip115to116);
    
    partial10bot := Tensor(act, proj111to10, projflip111to10) * Tensor(act, e10red, Tensor(act, Cup(B,4)`stdmor, eflip10red))*b10;
    partial111bot := Tensor(act, proj112to111, projflip112to111) * Tensor(act, e111red, Tensor(act, Cup(B,3)`stdmor, eflip111red)) * partial10bot;
    partial112bot := Tensor(act, proj113to112, projflip113to112) * Tensor(act, e112red, Tensor(act, Cup(B,2)`stdmor, eflip112red)) * partial111bot;
    partial113bot := Tensor(act, proj114to113, projflip114to113) * Tensor(act, e113red, Tensor(act, Cup(B,1)`stdmor, eflip113red)) * partial112bot;
    partial114bot := Tensor(act, proj115to114, projflip115to114) * Tensor(act, e114red, Tensor(act, Cup(B,2)`stdmor, eflip114red)) * partial113bot;
    partial115bot := Tensor(act, proj116to115, projflip116to115) * Tensor(act, e115red, Tensor(act, Cup(B,1)`stdmor, eflip115red)) * partial114bot;
    
    trace116temp := partial115top * Tensor(act, e116red, root^6*eflip116);
    partial10 := trace116temp * partial115bot;
    
    dim116 := partial10`mat[1,1]/trace10`mat[1,1];
    
    T2 := Time(T);
    S := GetMaximumMemoryUsage();
    Sprintf("The dimension of e1212132121432121 is %o. Total time for the calculation took %o, used space was %o.", dim116, T2, S);
    
end procedure;
