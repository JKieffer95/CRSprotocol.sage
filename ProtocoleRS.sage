
# coding: utf-8


#packages
from sage.databases.db_modular_polynomials import ModularPolynomialDatabase


def SystemDefinition(L):
    #On cherche des données initiales ayant les bonnes propriétés.
    #A éviter : les courbes supersingulières, les j-invariants 0 et 1728, les nombres premiers divisant le discriminant
    #et la trace, les nombres premiers inertes.
    while True :
        j_init=F.random_element()
        E_init=EllipticCurve_from_j(j_init)
        P=E_init.frobenius_polynomial()
        Discr=P.discriminant()
        Trace=-P[1]
        test=True
        for l in L:
            if kronecker_symbol(Discr,l)<>1 or Trace%l==0: test=False
        if test and E_init.is_ordinary:
            V=[]
            for l in L:
                v=P.roots(FiniteField(l))[0][0]
                V.append(v)
            return j_init,V
            break
        else:
            continue
            
#Problème : apparemment cette condition de trace interdit parfois certains premiers, par ex. 3 ici


def get_psi_l(l):
    DBMP=ClassicalModularPolynomialDatabase()
    return DBMP[l]



def find_scaling(E_init,E_1,l):
    for a in F:
        try:
            assert a<>0
            E_2=E_1.scale_curve(a)
            phi=EllipticCurveIsogeny(E_init,None,E_2,degree=l)
            return a
            break
        except: continue



#ne contrôle que la coordonnée x, donc la direction échoue si la trace est nulle
#pour l'instant le facteur de scaling est cherché de façon exhaustive, il reste à utiliser les formules de Schoof
#pour déterminer le facteur de scaling directement

#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728

#!!! Ce code semble ne pas fonctionner. Je constate certains retours en arrière. De plus dans certains cas le polynôme 
#n'a pas de racines ??
def first_step(j,l,v):
    E=EllipticCurve_from_j(j)
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    (r_1,r_2)=pol.roots()
    j_1=r_1[0]
    j_2=r_2[0]
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    try:
        E_1=EllipticCurve_from_j(j_1)
        if not E.is_isogenous(E_1): E_1=E_1.quadratic_twist()
        a=find_scaling(E,E_1,l)
        if a not in F : raise ValueError
        E_1=E_1.scale_curve(a)
        phi_1=EllipticCurveIsogeny(E,kernel=None,codomain=E_1,degree=l)
        K_1=phi_1.kernel_polynomial()
        Fext1.<t>=K_1.splitting_field()
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert t**p==f_1(t)
        return j_1
    except AssertionError:
        E_2=EllipticCurve_from_j(j_2)
        if not E.is_isogenous(E_2): E_2=E_2.quadratic_twist()
        return j_2



#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728
def following_step(j,l,j_prec):
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    (r_1,r_2)=pol.roots()
    j_1=r_1[0]
    j_2=r_2[0]
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    if j_1<>j_prec:
        return j_1
    else:
        return j_2



def RouteComputation(j_init,R,L,V):
    #j_init : le j-invariant de la courbe initiale
    #L : la liste de nombres premiers considérés
    #R : la route, i.e. liste du nombre de pas pour chaque nombre premier
    #V : la liste des valeurs propres donnant le sens positif
    j_0=j_init
    for n in range(len(L)):
        l=L[n]
        v=V[n]
        r=R[n]
        if r>0:
            j_1=first_step(j_0,l,v)
            for k in range(1,r):
                j_2=following_step(j_1,l,j_0)
                j_0=j_1
                j_1=j_2
            j_0=j_1
        else:
            pass
    return j_0



#utilisé dans IsogenyGraph
#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728

#Remarque : on pourrait réutiliser le code de followingstep pour construire IsogenyGraph
def neighbors(j,l):
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    assert j<>0 and j<>1728
    else:
        (r_1,r_2)=pol.roots()
        j_1=r_1[0]
        j_2=r_2[0]
        return j_1,j_2



#utile pour la fonction qui suit
def update(D,j_1,j_2,l):
    if j_1 in D.keys():
        D[j_1][j_2]=l
    else:
        D[j_1]={j_2: l}


def IsogenyGraph(j_0,L):
    #on construit un graphe au format "dict_of_dicts". L est une liste non vide de (petits) premiers totalement scindés 
    #dans \Q(\sqrt(Discr))
    Dict={}
    E=EllipticCurve_from_j(j_0)
    assert E.is_ordinary()
    Discr=E.frobenius_polynomial().discriminant()
    for l in L:
        assert kronecker_symbol(Discr,l)==1
    for l in L:
        flag=j_0
        j_1,j_2=neighbors(j_0,l)
        update(Dict,j_0,j_1,l)
        j=j_1
        while j<>j_0:
            j_1,j_2=neighbors(j,l)
            if j_1<>flag:
                update(Dict,j,j_1,l)
                flag=j
                j=j_1
            else:
                update(Dict,j,j_2,l)
                flag=j
                j=j_2
    G=Graph(Dict,format='dict_of_dicts')
    return G

