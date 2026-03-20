//Short file to show how one can calculate the H-cell structure and the Grothendieck ring of an H-cell. We mostly use tha package ASLoc.spec and added just a few function.

//Load ASLoc
//AttachSpec("ASLoc.spec");
load "cell_matrix/cell_matrix_grothendieck.m";

//Choose your favorite CoxeterGroup
W := CoxeterGroup(GrpFPCox, "E6");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);


//Now choose the index of your two-sided Cell you want to investigate:
index := 14;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

//M is a matrix giving you the number of elements in each H-cell
//Lindex is an array giving you which left cells of left lie in twoSided
//Rindex is the same for right cells
//list contains tuples of indices that lets you create any (i,j)-Hcell via:

i := 2;
j := 3;

Hcell := (Components(left)[Lindex[i]] meet Components(right)[Rindex[j]]);

//If you want to get the GrothendieckRing of an H-cell you need to take a diagonal one
k := 1;

Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];

//Output is a 3-dimensional array. you need to put in the a-value
//In the middle cell of type H_4 the computations inside ASLoc take too long; We advise the examples below for getting all other Grothendieck rings we mentioned
a:= 3;
Hsorted, GR := GrothendieckRing(C, Hcell, a);
//The entry l in position (i,j,k) tell us that in the produkt of the i-th element of Hsorted with the j-th Element the k-th Element occurs l times. We sort the list by the length of the elements

//Example 1 Cell 6 in Type D4: Vec(Z/2Z);
W := CoxeterGroup(GrpFPCox, "D4");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 6;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

k := 1;
Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];
Hsorted, GR := GrothendieckRing(C, Hcell, 3);

//Example 2 Cell 6 in Type H3: Fibonacci Ring;
W := CoxeterGroup(GrpFPCox, "H3");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 2;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

k := 1;
Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];
Hsorted, GR := GrothendieckRing(C, Hcell, 6);

//Example 2a Cell 2 in Type I2(n): SO(3)_{n-2};
W := CoxeterGroup(GrpFPCox, "I2(8)");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 2;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

k := 1;
Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];
Hsorted, GR := GrothendieckRing(C, Hcell, 1);

//Example 3 Cell 5 in Type F4: Rep(S4);
//This takes a couple minutes as the elements have lengths 8-20
W := CoxeterGroup(GrpFPCox, "F4");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 6;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

k := 1;
Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];
Hsorted, GR := GrothendieckRing(C, Hcell, 4);

//Example 4 Cell 13 in Type B6;
W := CoxeterGroup(GrpFPCox, "B6");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 7;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

//Example 5 Cell 9 in Type E6: Rep(S3);
//This is not implemented as idempotents; it is just for completions sake
//Computation of Cells takes a little longer; Grothendieck ring around an hour
W := CoxeterGroup(GrpFPCox, "E6");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 9;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

k := 1;
Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];
Hsorted, GR := GrothendieckRing(C, Hcell, 7);

//Example 6 Cell 7 in Type H4:
//This takes very long
W := CoxeterGroup(GrpFPCox, "H4");
HAlg := IHeckeAlgebra(W);
C := CanonicalBasis(HAlg);
left, right, twoSided := Cells(C);
index := 7;
M, Lindex, Rindex, list := CreateHcellStructure(left, right, twoSided, index);

// Analyze the block structure
blocks := AnalyzeBlockStructure(M);
printf "Block structure: %o\n", blocks;

k := 1;
Hcell := Components(left)[list[k][1]] meet Components(right)[list[k][2]];
Hsorted, GR := GrothendieckRing(C, Hcell, 6);
