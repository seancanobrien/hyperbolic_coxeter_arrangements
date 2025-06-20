Last := function(L)
        return L[Length(L)];
    end;

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
        return 0;  # No complement found
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
    local l, m, mid, half;
    l := LengthWord(word);
    m := (l+1)/2;
    mid := Subword(word,m,m);
    if l<2 then
        half := IdWord;
    else
        half := Subword(word, 1, m-1);
    fi;
    return [mid, half];
end;

# returns a list of factors of the word without any ^+-1 data
FactorsOfWord := function(word)
    local output, i, cur_letter;
    output := [];
    for i in [1..LengthWord(word)] do
        cur_letter := Subword(word, i, i);
        Add(output, cur_letter);
    od;
    return output;
end;

LessEqualMatrix := function(A, B)
  local i, j;
  for i in [1..Length(A)] do
    for j in [1..Length(A[i])] do
      if A[i][j] > B[i][j] then
        return false;
      fi;
    od;
  od;
  return true;
end;

MaxAlternatingLengthMatrix := function(word, gens)
    local rank, output_matrix, i, j, pair, alt_length;
    rank := Length(gens);
    # initialise output matrix 
    output_matrix := List([1..rank], i -> List([1..rank], j -> 1));
    for i in [1..rank] do
        for j in [i+1..rank] do
            pair := [gens[i], gens[j]];
            alt_length := MaxAlternatingLengthOfPair(word, pair);
            output_matrix[i][j] := alt_length;
            output_matrix[j][i] := alt_length;
        od;
    od;
    return output_matrix;
end;

MaxAlternatingLengthOfPair := function(word, pair)
    local pair_and_invs, factors, maxlen, curlen, i;
    pair_and_invs := [pair[1], pair[2], pair[1]^(-1), pair[2]^(-1)];
    factors := FactorsOfWord(word);
    if Length(factors) = 2 then
        if factors[1] in pair_and_invs and factors[2] in pair_and_invs then
            return 2;
        else
            return 0;
        fi;
    elif Length(factors) = 1 then
        return 0;
    fi;
    maxlen := 0;
    curlen := 0;
    for i in [1..Length(factors)] do
        if factors[i] in  pair_and_invs then
            curlen := curlen + 1;
            if curlen > 1 then
                maxlen := Maximum(maxlen, curlen);
            fi;
        else
            curlen := 0;
        fi;
    od;
    return maxlen;
end;

MaxAlternatingLength := function(word)
    local factors, i, first_letter, second_letter, current_alternating_pair, maxlen, curlen;
    # Extract the list of [generator, exponent] pairs
    factors := FactorsOfWord(word);
    if Length(factors) < 3 then
        return Length(factors);
    fi;
    first_letter := factors[1];
    second_letter := factors[2];
    current_alternating_pair := [first_letter, first_letter^(-1), second_letter, second_letter^(-1)];
    maxlen := 2;
    curlen := 2;
    # If the word is length 1 or 2 then the max alternating sequence is just 1 or 2
    for i in [3..Length(factors)] do
        if factors[i] in current_alternating_pair then
            curlen := curlen + 1;
            maxlen := Maximum(maxlen, curlen);
        else
            first_letter := factors[i-1];
            second_letter := factors[i];
            current_alternating_pair := [first_letter, first_letter^(-1), second_letter, second_letter^(-1)];
            curlen := 2;
        fi;
    od;
    return maxlen;
end;

WriteWordToFile := function(filename, word)
    local i, letter, result;
    result := "";
    # Iterate over each character in the word
    for i in [1..LengthWord(word)-1] do
        letter := Subword(word, i, i);
        AppendTo(filename, letter, "*");
    od;
    AppendTo(filename, Subword(word, LengthWord(word), LengthWord(word)));
end;

PrintGroupedWords := function(grouped_words, gens, coxeter_matrix, file_name)
    local i, j, group, word, midHalf, max_alt_lengths;
    for i in [1..Length(grouped_words)] do
        group := grouped_words[i];
        for j in [1..Length(group)] do
            word := group[j];
            midHalf := GetMidAndHalf(word);
            max_alt_lengths := MaxAlternatingLengthMatrix(word, gens);
            AppendTo(file_name,
                max_alt_lengths,
                " -- ",
                LessEqualMatrix(max_alt_lengths, coxeter_matrix),
                " -- ",
                midHalf[1],
                ": "
                );
            if LengthWord(midHalf[2]) > 0 then
                WriteWordToFile(file_name, midHalf[2]);
            else
                AppendTo(file_name, "IdWord");
            fi;
            AppendTo(file_name, "\n");
        od;
        AppendTo(file_name, "\n");
        AppendTo(file_name, "\n");
    od;
end;

GroupIntoEquivalenceClasses := function(list, isEqual)
    local classes, obj, class, i, j, matched;
    classes := [];
    for i in [1..Length(list)] do
        obj := list[i];
        matched := false;
        for j in [1..Length(classes)] do
            class := classes[j];
            # Compare to representative (first element)
            if isEqual(obj, class[1]) then
                Add(class, obj);
                matched := true;
                # Can't use break, so simulate exit
                j := Length(classes);
            fi;
        od;
        if not matched then
            Add(classes, [obj]);
        fi;
    od;
    return classes;
end;

WordsEqualAfterHom := function(word1, word2, hom)
    return hom(word1)=hom(word2);
end;

alph :=[
"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"
];

MakeFreeGroup := function(n)
    local names, F;
    names := List([1..n], i -> alph[i]);  # "a", "b", ...
    F := FreeGroup(names);
    return F;
end;

MakeHom := function(F, W)
    return function(x)
        return MappedWord(x, Generators(F), Generators(W));
    end;
end;

PrintHurwitzWordsGroupedByCox := function(coxeter_matrix, braid_length, filename)
    local W, rank, gens, F, hom, coxeter_equality, hurwitz_factorisations,
        hurwitz_words, grouped_hurwitz_words;
    W := CoxeterGroupByCoxeterMatrix(coxeter_matrix);
    rank := Rank(W);
    F := MakeFreeGroup(rank);
    hom:= MakeHom(F, W);
    coxeter_equality := function(word1, word2)
        return hom(word1) = hom(word2);
    end;
    # main logic of function
    hurwitz_factorisations := List(GenerateWords(List([1..rank-1], x -> [-x,x]), braid_length), action -> MultipleHurwitzFreeGroup(Generators(F), action));
    hurwitz_words := Set(Concatenation(hurwitz_factorisations));
    grouped_hurwitz_words := GroupIntoEquivalenceClasses(hurwitz_words, coxeter_equality);
    # printing to file
    PrintTo(filename, "");  # clear the file
    AppendTo(filename, "W = ", W, "\n");
    AppendTo(filename, "Max braid length = ", braid_length, "\n");
    AppendTo(filename, "Total of ", Length(grouped_hurwitz_words), " different coxeter group elements (grouped by line breaks).\n");
    AppendTo(filename, "Notation: 'y: x' means xyx^(-1)\n");
    AppendTo(filename, "=========================================================\n\n");
    PrintGroupedWords(grouped_hurwitz_words, Generators(F), coxeter_matrix, filename);
end;

# 3-5-3 Coxeter group
W_353 :=    [
    [1,3,2,2],
    [3,1,5,2],
    [2,5,1,3],
    [2,2,3,1]
    ];

W_all_2 :=
    [
    [1,2,2,2],
    [2,1,2,2],
    [2,2,1,2],
    [2,2,2,1]
    ];

W_all_3 :=
    [
    [1,3,3,3],
    [3,1,3,3],
    [3,3,1,3],
    [3,3,3,1]
    ];

W_all_4 :=
    [
    [1,4,4,4],
    [4,1,4,4],
    [4,4,1,4],
    [4,4,4,1]
    ];

W_random_large_type :=
    [
    [1,4,6,7],
    [4,1,3,8],
    [6,3,1,3],
    [7,8,3,1]
    ];


# PrintHurwitzWordsGroupedByCox(W_353, 5, "words_353.csv");
# PrintHurwitzWordsGroupedByCox(W_all_2, 6, "words_all_2.csv");
# PrintHurwitzWordsGroupedByCox(W_all_3, 6, "words_all_3.csv");
# PrintHurwitzWordsGroupedByCox(W_all_4, 6, "words_all_4.csv");
PrintHurwitzWordsGroupedByCox(W_random_large_type, 6, "words_random_large_type.csv");

F := MakeFreeGroup(3);
a := F.1;; b := F.2;; c := F.3;;

