//Function that sorts a matrix to create block structure; tracks labels in Lindex and Rindex
function SortMatrixByBlocks(M, Lindex, Rindex)
    // Check if the matrix is square and indices have correct length
    n := Nrows(M);
    if n ne Ncols(M) or n ne #Lindex or n ne #Rindex then
        error "The matrix must be square and indices must match matrix dimensions";
    end if;

    // Create a list of tuples: (diagonal value, row/col index)
    diagonalValues := [];
    for i := 1 to n do
        Append(~diagonalValues, <M[i,i], i>);
    end for;

    // Sort the list based on diagonal values
    Sort(~diagonalValues);

    // Create copies of the original matrix and indices
    sortedM := M;
    sortedLindex := Lindex;
    sortedRindex := Rindex;

    // Perform row and column swaps
    for i := 1 to n do
        currentIndex := diagonalValues[i][2];
        if i ne currentIndex then
            // Swap rows in matrix
            tempRow := sortedM[i];
            sortedM[i] := sortedM[currentIndex];
            sortedM[currentIndex] := tempRow;

            // Swap columns in matrix
            tempCol := Transpose(sortedM)[i];
            for j := 1 to n do
                sortedM[j,i] := sortedM[j,currentIndex];
                sortedM[j,currentIndex] := tempCol[j];
            end for;

            // Swap elements in Lindex and Rindex
            tempL := sortedLindex[i];
            sortedLindex[i] := sortedLindex[currentIndex];
            sortedLindex[currentIndex] := tempL;

            tempR := sortedRindex[i];
            sortedRindex[i] := sortedRindex[currentIndex];
            sortedRindex[currentIndex] := tempR;

            // Update the remaining indices in diagonalValues
            for k := i+1 to n do
                if diagonalValues[k][2] eq i then
                    diagonalValues[k][2] := currentIndex;
                end if;
            end for;
        end if;
    end for;

    // Create the sequence of tuples
    sortedIndices := [<sortedLindex[i], sortedRindex[i]> : i in [1..n]];

    return sortedM, sortedIndices;
end function;

//SortMatrixByBlockValue: Sort rows/columns to create block structure
//Sort by diagonal value (descending), then by row pattern within each group
function SortMatrixByBlockValue(M, Lindex, Rindex)
    n := Nrows(M);
    if n ne Ncols(M) or n ne #Lindex or n ne #Rindex then
        error "The matrix must be square and indices must match matrix dimensions";
    end if;

    // Build sort key: (diagonal value descending, sorted row pattern)
    rowData := [];
    for i in [1..n] do
        sortedRow := Sort([M[i,j] : j in [1..n]]);
        Append(~rowData, <-M[i,i], sortedRow, i>);
    end for;

    Sort(~rowData);
    perm := [rowData[i][3] : i in [1..n]];

    // Apply row permutation
    newM := ZeroMatrix(BaseRing(M), n, n);
    newL := [];
    newR := [];
    for i in [1..n] do
        for j in [1..n] do
            newM[i, j] := M[perm[i], j];
        end for;
        Append(~newL, Lindex[perm[i]]);
        Append(~newR, Rindex[perm[i]]);
    end for;

    // Apply same column permutation
    sortedM := ZeroMatrix(BaseRing(newM), n, n);
    for i in [1..n] do
        for j in [1..n] do
            sortedM[i, j] := newM[i, perm[j]];
        end for;
    end for;

    sortedIndices := [<newL[i], newR[i]> : i in [1..n]];
    return sortedM, sortedIndices;
end function;

//Analyze block structure: returns 2D representation of actual blocks
//Shows block values and dimensions in matrix form (e.g., "2_6,6" = value 2 in 6x6 block)
function AnalyzeBlockStructure(M)
    n := Nrows(M);

    // Find row block boundaries (consecutive rows with same pattern)
    rowBlocks := [];
    i := 1;
    while i le n do
        rowStart := i;
        rowPattern := [M[i, j] : j in [1..n]];

        // Find rows with identical pattern
        while i lt n do
            nextPattern := [M[i+1, j] : j in [1..n]];
            if nextPattern eq rowPattern then
                i := i + 1;
            else
                break;
            end if;
        end while;

        rowEnd := i;
        Append(~rowBlocks, <rowStart, rowEnd>);
        i := i + 1;
    end while;

    // Find column block boundaries
    colBlocks := [];
    j := 1;
    while j le n do
        colStart := j;
        colPattern := [M[i, j] : i in [1..n]];

        // Find columns with identical pattern
        while j lt n do
            nextPattern := [M[i, j+1] : i in [1..n]];
            if nextPattern eq colPattern then
                j := j + 1;
            else
                break;
            end if;
        end while;

        colEnd := j;
        Append(~colBlocks, <colStart, colEnd>);
        j := j + 1;
    end while;

    // Build block matrix representation
    result := [];
    for rb in rowBlocks do
        row := [];
        for cb in colBlocks do
            // Get the value of this block (all entries should be the same)
            val := M[rb[1], cb[1]];
            rowSize := rb[2] - rb[1] + 1;
            colSize := cb[2] - cb[1] + 1;
            Append(~row, Sprintf("%o_%o,%o", val, rowSize, colSize));
        end for;
        Append(~result, row);
    end for;

    return result;
end function;

//Compute a matrix desribing the number of elements in the H-cells of given twoSided cell and further information
function CreateHcellStructure(left, right, twoSided, index)
    LR := Components(twoSided)[index];
    //Find all left cells contained in LR
    //Lindex := [i : i in[1..#Components(left)] | #(LR meet Components(left)[i]) gt 0];

    Lindex := Setseq({left`CoxToCompIdx[x] : x in LR});

    //Find the corresponding right cells
    Rindex := [];

    for i in Lindex do
        leftcell := Components(left)[i];
        rightcell := {x^-1 : x in leftcell};
        hcell := leftcell meet rightcell;
        elt := Random(hcell);
        Append(~Rindex, right`CoxToCompIdx[elt]);
    end for;

    size := #Lindex;

    M := ZeroMatrix(Integers(), size, size);

    for i in [1..size] do
        for j in [1..size] do
            M[i,j] := #(Components(left)[Lindex[i]] meet Components(right)[Rindex[j]]);
        end for;
    end for;

    MM, list := SortMatrixByBlockValue(M, Lindex, Rindex);

    return MM, Lindex, Rindex, list;
end function;

function GrothendieckRing(C, H, a)
    // Compute the Grothendieck ring
    cell := Setseq(H);
    lengthCompare := func<x, y | #x - #y>;
    cell := Sort(cell, lengthCompare);
    size := #cell;

    result := [[[0: i in [1..size]]: j in [1..size]]: k in [1..size]];

    for i in [1..size] do
        for j in [1..size] do
            x := cell[i];
            y := cell[j];
            product := C.x * C.y;
            //Collect all possible summands
            keys := H meet Keys(product`Terms);

            // Loop over all terms in Keys (assuming Keys is a set or sequence)
            for key in keys do
                pol := product`Terms[key];
                if Degree(pol) eq a then
                    k :=Index(cell, key);
                    l :=  Coefficient(pol, -a);
                    result[i][j][k] := l;
                end if;
            end for;
        end for;
    end for;
    return cell, result;
end function;
