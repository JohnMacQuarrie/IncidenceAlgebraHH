Indeterminate = libgap.eval("I:=function(x,y) return Indeterminate(x,y); end;");
StringFormatted = libgap.eval("S:=function(x,y,z,w) return StringFormatted(x,y,z,w);end;");
StF = libgap.eval("St:=function(x,y,z) return StringFormatted(x,y,z);end;");
VectorSpace=libgap.eval("V:=function(x,y,z) return VectorSpace(x,y,z);end;");
Mapadeciclos = libgap.eval("Mapadeciclos:=function(Source,Range,cycle)local Im,i,f,D;D:=GeneratorsOfVectorSpace(Source);Im:=[];for i in [1..Length(cycle)] do Add(Im, LinearCombination(Basis(Range), cycle[i][1])); od;f:=LeftModuleGeneralMappingByImages(Source, Range, D, Im);return f;end;");
Z_CycleSpace = libgap.eval("Z_CycleSpace:=function(cycles,zlist,Source,f)local K, zSubspace, i, j, aux, VerticesOfCycles, CoefficientsOfCycles, T;CoefficientsOfCycles:=[]; if Length(zlist)>0 then K:=BasisVectors(Basis((Kernel(RestrictedMapping(f, Subspace(Source,zlist))))));for i in [1..Length(K)] do Add(CoefficientsOfCycles,Coefficients(Basis(Source), K[i]));od;fi;T:=CoefficientsOfCycles;return T;end;");
BasisComplement = libgap.eval("BasisComplement:=function(Aux_Bzminus,Aux_Ciplus, i, OurDomain,OurField) local F,Kzminus,t,BC; BC:=[]; F:=OurField^Length(OurDomain);if Length(Aux_Bzminus)>0 then KZminus:=Subspace(F, Aux_Bzminus);for t in [1..Length(Aux_Ciplus[i][1])] do if (Aux_Ciplus[i][1][t] in KZminus)=false then Add(BC, [Aux_Ciplus[i][1][t], Aux_Ciplus[i][2]]); Add(Aux_Bzminus, Aux_Ciplus[i][1][t]); KZminus:=Subspace(F, Aux_Bzminus);fi;od; else for t in [1..Length(Aux_Ciplus[i][1])] do Add(BC, [Aux_Ciplus[i][1][t],Aux_Ciplus[i][2]]);od; fi; return BC;end;")

def iCycles(X, c):
    # c = characterist of OurField
    G = X.with_bounds().canonical_label()
    h = G.minimal_elements()[0]
    y = G.maximal_elements()[0]
    xplus = G.upper_covers(h)

    if c == 0:
        OurField = QQ
    else:
        OurField = GF(c)

    candidates = list(G)
    q = 1
    OurDomain = [Indeterminate(OurField, "x")]
    iminusCycles = [[1,h]]

    iCycles = []
    for j in xplus:
        iCycles.append([[1], j])

    if len(iCycles) == 0:
        q = -1
    else:
        q += 1

    while q != -1:
        OurCodomain = OurDomain
        OurDomain = []

        if q == 2:
            for i in range(len(iCycles)):
                OurDomain.append(Indeterminate(OurField, StF("[{}, {}]", OurCodomain[0], iCycles[i][1])))
        else:
            for i in range(len(iCycles)):
                OurDomain.append(Indeterminate(OurField, StringFormatted("[w^{}_{}, {}]", q-1 , i, iCycles[i][1])))

        SourceSpace = VectorSpace(OurField, OurDomain,"basis")
        RangeSpace = VectorSpace(OurField,OurCodomain,"basis")
        f = Mapadeciclos(SourceSpace,RangeSpace,iCycles)

        iminusCycles = []
        for i in range(len(iCycles)):
            iminusCycles.append([iCycles[i][0],Integer(iCycles[i][1])])

        iCycles = []
        Aux_Ciplus = []

        for k in candidates:
            zSubspace=[]
            for i in range(len(iminusCycles)):
                if G.is_less_than(iminusCycles[i][1], k):
                    zSubspace.append(OurDomain[i])
            if zSubspace != []:
                T = Z_CycleSpace(iminusCycles,zSubspace,SourceSpace,f)
                if T != []:
                    Aux_Ciplus.append([T, k])

        I = list(range(len(Aux_Ciplus)))

        for i in I:
            Aux_Bzminus = set([])
            for j in I:
                if Aux_Ciplus[j][1] in G.lower_covers(Aux_Ciplus[i][1]):
                    Aux_Bzminus.update(Aux_Ciplus[j][0])
            BC = BasisComplement(list(Aux_Bzminus),Aux_Ciplus, i+1, OurDomain,OurField)
            if len(BC) != 0:
                [iCycles.append(a) for a in BC]

        if len(iCycles) == 0:
            q = -1
        else:
            q += 1


import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning)

def Send_poset_to_Magma(G):
    X = G.with_bounds().canonical_label()
    xstar = X.minimal_elements()[0]
    m = X.height()

    Z = X.relabel()
    Z = Z.relabel(lambda s: s + 1)
    Q = DiGraph([(x, y, 'x' + str(x) + str(y)) for x, y in Z.cover_relations()])
    SG = Q.path_semigroup()
    A = SG.algebra(ZZ)

    rels = []
    for a, b in Z.relations():
        if Q.in_degree(b) > 1 and Q.out_degree(a) > 1:
            paths = Q.all_paths(a, b)
            if len(paths) > 1:
                prod_paths = [
                    A.prod(A(Q.edge_label(pa[i], pa[i + 1])) for i in range(len(pa) - 1))
                    for pa in paths
                ]
                rels += [prod_paths[0] - pi for pi in prod_paths[1:]]

    n = len(Q)
    var(' '.join([f'e{i}' for i in range(1, n + 1)]))
    V = [eval(f'e{i}') for i in range(1, n + 1)]

    Lista = Q.num_verts(), [list(e) for e in Q.edges()]
    L = Lista[1]
    T = []
    for element in L:
        a, b, x = element
        V.append(var(x))
        T.append((a, b))

    vars_str = "F<" + ", ".join(str(v) for v in V) + ">"
    free_algebra_str = f"FreeAlgebra(RationalField(), {len(V)})"
    rels_str = ", ".join(str(r) for r in rels)
    pairs_str = ", ".join(f"<{a},{b}>" for a, b in T)

    magma.eval(f"{vars_str} := {free_algebra_str};")
    magma.eval(f"BA := BasicAlgebra(F, [{rels_str}], {n}, [{pairs_str}]);")
    magma.eval("S_X := SimpleModule(BA,1);")
    magma.eval(f"m_X := {int(m)};")

import time
def compute_time(fn, *args, **kw):
    t0 = time.perf_counter()
    fn(*args, **kw)
    return time.perf_counter() - t0