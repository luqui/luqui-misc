
\!\(TraditionalForm\`EFG[
      X_, \ {u_, v_}]\  := \ \ With[{xu = D[X, u], 
        xv = D[X, v]}, \[IndentingNewLine]{xu . xu, xu . xv, xv . xv}]\)

\!\(TraditionalForm\`UnitNormal[X_, \ {u_, \ v_}]\  := \ 
    With[\[IndentingNewLine]{Z = 
          Cross[D[X, u], D[X, v]]}, \[IndentingNewLine]Z/Z . Z]\)

\!\(TraditionalForm\`lmn[X_, \ {u_, \ v_}]\  := \ 
    With[{U = UnitNormal[X, {u, v}]}, \[IndentingNewLine]{U . D[X, u, u], 
        U . D[X, u, v], U . D[X, v, v]}]\)

\!\(\*FormBox[
  RowBox[{\(shape[X_, {u_, v_}]\), ":=", " ", 
    RowBox[{"Module", "[", 
      RowBox[{\({\[CapitalEpsilon], F, G, l, m, n}\), ",", 
        "\[IndentingNewLine]", 
        RowBox[{\({\[CapitalEpsilon], F, G}\  = \ EFG[X, {u, v}]\), ";", 
          "\[IndentingNewLine]", \({l, m, n} = lmn[X, {u, v}]\), ";", 
          "\[IndentingNewLine]", 
          RowBox[{\(1\/\(\[CapitalEpsilon]\ G - F\^2\)\), 
            RowBox[{"(", GridBox[{
                  {\(G\ l\  - \ F\ m\), \(G\ m - F\ n\)},
                  {\(\[CapitalEpsilon]\ n - F\ l\), \(\[CapitalEpsilon]\ n - 
                      F\ m\)}
                  }], ")"}]}]}]}], "]"}]}], TraditionalForm]\)
