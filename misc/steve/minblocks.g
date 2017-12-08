#
# MinBlocks( <G>, <B> ) find the minimal (linear) <G>-invariant block system such that
#                       <B> lies in a block.
#
#  Based on the implementation in the GAP3 matrix package, reimplemented with new bugs
#  by Steve Linton, June 2006
#
#
#


MinBlocks := function(G, B)
    local   equateBlocks,  realBlock,  mergeBlocks,  Bc,  o,  res,
            eb,  pivots,  i,  blocks,  coeffs,  gens,  ngens,  invs,
            igen,  p,  blockact,  blockdel,  k,  v,  b1,  gen,  w,
            w1,  coeff,  j,  x,  y,  b2,  hits,  nblocks,  numbering,
            live,  perms,  perm;
    equateBlocks := function(b1,b2)
        local   i,  b2im,  b2im2,  b1im;
        b1 := realBlock(b1);
        b2 := realBlock(b2);
        if b1 = b2 then
            return;
        fi;
        blockdel[b2] := b1;
        for i in [1..Length(blockact[b1])] do
            b2im := realBlock(blockact[b2][i]);
            if b2im <> 0 then
                b1 := realBlock(b1);
                b2im2 := realBlock(blockact[b2im][invs[i]]);
                if b2im2 <> 0 then
                    equateBlocks(b1,b2im2);
                    b2im := realBlock(b2im);
                    b1 := realBlock(b1);
                fi;
                blockact[b2im][invs[i]] := b1;
                b1im := realBlock(blockact[b1][i]);
                if b1im = 0 then
                    blockact[b1][i] := b2im;
                else
                    equateBlocks(b1im,b2im);
                fi;
            fi;
        od;
    end;

    realBlock := function(b)
        if b = 0 then
            return 0;
        fi;
        if IsBound(blockdel[b]) then
            blockdel[b] := realBlock(blockdel[b]);
            return blockdel[b];
        else
            return b;
        fi;
    end;

    mergeBlocks := function(set)
        local   i;
        for i in [2..Length(set)] do
            equateBlocks(set[1],set[i]);
        od;
       blocks := List(blocks,realBlock);
    end;

    Bc := List(B,ShallowCopy);
    o := One(B[1][1]);
    ConvertToMatrixRep(Bc);
    res := SemiEchelonMatTransformation(Bc);
    eb := List(res.vectors,ShallowCopy);
    pivots := [];
    for i in [1..Length(res.heads)] do
        if res.heads[i] <> 0 then
            pivots[res.heads[i]]:= i;
        fi;
    od;
    blocks := List(eb, x->1);
    coeffs := ShallowCopy(res.coeffs);
    gens := ShallowCopy(GeneratorsOfGroup(G));
    ngens := Length(gens);
    invs := [];
    for i  in [1..ngens] do
        if not IsBound(invs[i]) then
            igen := gens[i]^-1;
            p := Position(gens, igen);
            if p = fail then
                Add(gens, igen);
                invs[i] := Length(gens);
                invs[Length(gens)] := i;
            else
                invs[i] := p;
                invs[p] := i;
            fi;
        fi;
    od;
    blockact := [List(gens, x->0)];
    blockdel := [];
    k := 1;
    while k <= Length(eb) do
        v := Bc[k];
        b1 := blocks[k];
        for i in [1..ngens] do
            gen := gens[i];
            w := v*gen;
            w1 := ShallowCopy(w);
            coeff := ZeroMutable(coeffs[Length(coeffs)]);
            for j in [1..Length(eb)] do
                p := pivots[j];
                x := w[p];
                if not IsZero(x) then
                    y := -x/eb[j][p];
                    AddCoeffs(w,eb[j],y);
                    AddCoeffs(coeff, coeffs[j],y);
                fi;
            od;
            p := PositionNonZero(w);
            if p <= Length(w) then
                Add(eb,w);
                Add(pivots,p);
                Add(coeff,o);
                Add(coeffs,coeff);
                Add(Bc,w1);
                b2 := realBlock(blockact[b1][i]);
                if b2 =  0 then
                    b2 := Length(blockact)+1;
                    Add(blockact,List(gens, x-> 0));
                    blockact[b1][i] := b2;
                    blockact[b2][invs[i]] := b1;
                fi;
                Add(blocks,b2);
            else
                hits := [];
                p := 0;
                while true do
                    p := PositionNonZero(coeff,p);
                    if p > Length(coeff) then
                        break;
                    fi;
                    AddSet(hits, realBlock(blocks[p]));
                od;
                b2 := realBlock(blockact[b1][i]);
                if Length(hits) = 1 and b2 = 0 then
                    blockact[b1][i] := hits[1];
                    blockact[hits[1]][invs[i]] := b1;
                else
                    if  b2 <> 0 then
                        AddSet(hits,b2);
                    fi;
                    if Length(hits) > 1 then
                        mergeBlocks(hits);
                        b1 := realBlock(b1);
                    fi;
                fi;
            fi;
        od;
        k := k+1;
    od;
    nblocks := 0;
    numbering := [];
    live := [];
    for i in [1..Length(blockact)] do
        if not IsBound(blockdel[i]) then
            nblocks := nblocks+1;
            numbering[i] := nblocks;
            Add(live,i);
        fi;
    od;
    perms := [];
    for i in [1..ngens] do
        perm := [];
        for j in live do
            Add(perm,numbering[blockact[j][i]]);
        od;
        Add(perms, PermList(perm));
    od;
    return rec(nblocks := nblocks,
               permact := perms,
               block := Bc{Filtered([1..Length(eb)], i->realBlock(blocks[i]) = 1)});
end;


