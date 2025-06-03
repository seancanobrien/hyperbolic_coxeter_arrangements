HurwitzActionCustomConj := function(i, R, conj)
    local result;
    result := ShallowCopy(R);

    if i > 0 then
        result[i] := conj(R[i], R[i + 1]);
        result[i + 1] := R[i];

    elif i < 0 then
        i := -i;
        result[i] := R[i + 1];
        result[i + 1] := conj(R[i + 1]^(-1), R[i]);

    fi;

    return result;
end;

FreeConjInv := function(a, b)
    return a * b * a^-1;
end;

HurwitzFreeGroup := function(i, R)
    return HurwitzActionCustomConj(i, R, FreeConjInv);
end;

MultipleHurwitzFreeGroup := function(R, listOfActions)
    if Length(listOfActions) = 0 then
        return R;
    else
        return MultipleHurwitzFreeGroup(
            HurwitzFreeGroup(Last(listOfActions), R),
            listOfActions{[1..Length(listOfActions)-1]}
        );
    fi;
end;

GenerateWords := function(alphabet, n)
    local flatAlphabet, ComplementPair, IsValidWord, allWords, validWords, word, pairs, i, sym, pair;

    # Flatten nested alphabet list
    flatAlphabet := Concatenation(alphabet);

    # Function to compute complement of a symbol
    ComplementPair := function(sym, alpha)
        local i, pair;
        for i in [1..Length(alpha)] do
            if sym in alpha[i] then
                pair := alpha[i];
                if sym = pair[1] then
                    return pair[2];
                else
                    return pair[1];
                fi;
            fi;
        od;
        return fail;  # No complement found
    end;

    # Function to check whether a word is valid
    IsValidWord := function(word)
        local j, sym1, sym2;
        for j in [1..Length(word)-1] do
            sym1 := word[j];
            sym2 := word[j+1];
            if sym1 = ComplementPair(sym2, alphabet) then
                return false;
            fi;
        od;
        return true;
    end;

    # Generate all words of length 0 to n
    allWords := [];
    for i in [0..n] do
        Append(allWords, Tuples(flatAlphabet, i));
    od;

    # Filter words
    validWords := Filtered(allWords, IsValidWord);

    return validWords;
end;

GetMidAndHalf := function(word)
    local l, m;
    l := Length(word);
    m := (l+1)/2;
    return [Subword(word,m,m), Subword(word,1,m-1)];
end;



F := FreeGroup("a", "b", "c");;
a := F.1;;  b := F.2;;  c := F.3;;

yo := List(GenerateWords([[-1,1],[-2,2]],5), action -> MultipleHurwitzFreeGroup([a,b,c], action));
yo := Set(Concatenation(yo));
yo := List(yo, GetMidAndHalf);

filename := "words.csv";
file := OutputTextFile(filename, false);  # 'false' means overwrite

for midHalf in yo do
    AppendTo(file, String(midHalf[1]), ": ", String(midHalf[2]), "\n");
od;

CloseStream(file);


