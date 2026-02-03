Indeterminate = libgap.eval("I:=function(x,y) return Indeterminate(x,y); end;")
StringFormatted = libgap.eval("S:=function(x,y,z,w) return StringFormatted(x,y,z,w);end;")
StF = libgap.eval("St:=function(x,y,z) return StringFormatted(x,y,z);end;")
VectorSpace = libgap.eval("V:=function(x,y,z) return VectorSpace(x,y,z);end;")
Cyclesmap = libgap.eval(
    "Cyclesmap:=function(Source,Range,cycle)local Im,i,f,D;"
    "D:=GeneratorsOfVectorSpace(Source);Im:=[];"
    "for i in [1..Length(cycle)] do "
    "Add(Im, LinearCombination(Basis(Range), cycle[i][1])); od;"
    "f:=LeftModuleGeneralMappingByImages(Source, Range, D, Im);"
    "return f;end;"
)
Z_CycleSpace = libgap.eval(
    "Z_CycleSpace:=function(cycles,zlist,Source,f)local K, zSubspace, i, j, aux, "
    "VerticesOfCycles, CoefficientsOfCycles, T;"
    "CoefficientsOfCycles:=[]; "
    "if Length(zlist)>0 then "
    "K:=BasisVectors(Basis((Kernel(RestrictedMapping(f, Subspace(Source,zlist))))));"
    "for i in [1..Length(K)] do "
    "Add(CoefficientsOfCycles,Coefficients(Basis(Source), K[i]));"
    "od;fi;"
    "T:=CoefficientsOfCycles;return T;end;"
)
BasisComplement = libgap.eval(
    "BasisComplement:=function(Aux_Bzminus,Aux_Ciplus, i, OurDomain,OurField) "
    "local F,Kzminus,t,BC; BC:=[]; "
    "F:=OurField^Length(OurDomain);"
    "if Length(Aux_Bzminus)>0 then "
    "KZminus:=Subspace(F, Aux_Bzminus);"
    "for t in [1..Length(Aux_Ciplus[i][1])] do "
    "if (Aux_Ciplus[i][1][t] in KZminus)=false then "
    "Add(BC, [Aux_Ciplus[i][1][t], Aux_Ciplus[i][2]]); "
    "Add(Aux_Bzminus, Aux_Ciplus[i][1][t]); "
    "KZminus:=Subspace(F, Aux_Bzminus);fi;od;"
    "else "
    "for t in [1..Length(Aux_Ciplus[i][1])] do "
    "Add(BC, [Aux_Ciplus[i][1][t],Aux_Ciplus[i][2]]);od; fi; "
    "return BC;end;"
)

def HH(P, c):
    G = P.with_bounds().canonical_label()
    y = G.maximal_elements()[0]
    h = G.minimal_elements()[0]
    xplus = G.upper_covers(h)

    if c == 0:
        OurField = QQ
    else:
        OurField = GF(c)

    candidates = list(G)

    countHH = 0
    q = 1

    OurDomain = [Indeterminate(OurField, "x")]
    iminusCycles = [[1, h]]

    iCycles = []
    for j in xplus:
        iCycles.append([[1], j])

    if len(iCycles) == 0:
        print(" dim HH^i = 0 for all i.")
        q = -1
    elif len(iCycles) == 1:
        print(" dim HH^0 = 1 for i=1.")
        print(" dim HH^i = 0 for i>1.")
        q = -1
    else:
        q += 1

    while q != -1:
        Ourcodomain = OurDomain
        OurDomain = []

        if q == 2:
            for i in range(len(iCycles)):
                OurDomain.append(
                    Indeterminate(
                        OurField,
                        StF("[{}, {}]", Ourcodomain[0], iCycles[i][1])
                    )
                )
        else:
            for i in range(len(iCycles)):
                OurDomain.append(
                    Indeterminate(
                        OurField,
                        StringFormatted("[w^{}_{}, {}]", q - 1, i, iCycles[i][1])
                    )
                )

        SourceSpace = VectorSpace(OurField, OurDomain, "basis")
        RangeSpace = VectorSpace(OurField, Ourcodomain, "basis")
        f = Cyclesmap(SourceSpace, RangeSpace, iCycles)

        iminusCycles = []
        for i in range(len(iCycles)):
            iminusCycles.append([iCycles[i][0], Integer(iCycles[i][1])])

        iCycles = []
        Aux_Ciplus = []

        for k in candidates:
            zSubspace = []
            for i in range(len(iminusCycles)):
                if G.is_less_than(iminusCycles[i][1], k):
                    zSubspace.append(OurDomain[i])
            if zSubspace != []:
                T = Z_CycleSpace(iminusCycles, zSubspace, SourceSpace, f)
                if T != []:
                    Aux_Ciplus.append([T, k])

        I = list(range(len(Aux_Ciplus)))

        for i in I:
            Aux_Bzminus = set([])
            for j in I:
                if Aux_Ciplus[j][1] in G.lower_covers(Aux_Ciplus[i][1]):
                    Aux_Bzminus.update(Aux_Ciplus[j][0])
            BC = BasisComplement(
                list(Aux_Bzminus), Aux_Ciplus, i + 1, OurDomain, OurField
            )
            if len(BC) != 0:
                for a in BC:
                    iCycles.append(a)

        if len(iCycles) == 0:
            print(" dim HH^i = 0 for i>", q - 3)
            q = -1
        else:
            for i in range(len(iCycles)):
                if iCycles[i][1] == y:
                    countHH += 1

            if q == 2:
                print(" dim HH^", q - 2, " = ", countHH + 1)
            else:
                print(" dim HH^", q - 2, " = ", countHH)

            q += 1
            countHH = 0