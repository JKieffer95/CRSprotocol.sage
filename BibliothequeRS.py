
# coding: utf-8

# In[ ]:

from sage.all import *
from BMSS import *


# In[19]:

#On cherche des données initiales ayant les bonnes propriétés.
#A éviter : les courbes supersingulières, les j-invariants 0 et 1728, les nombres premiers divisant le discriminant
#et la trace, les nombres premiers inertes.
#A utiliser pour p petit
def SystemDefinition(L,K):
    """Cette fonction prend en argument :
    -une liste de nombres premiers L,
    -un corps fini K,
    et renvoie un triplet E_init,j_init,V où
    -E_init est une courbe elliptique sur K de j-invariant j_init,
        telle que les éléments de L sont Elkies et ne divisent pas la trace,
    -V est la liste des couples (v_1,v_2) des valeurs propres du Frobenius modulo l."""
    for k in range(50):
        j_init=K.random_element()
        E_init=EllipticCurve(j=j_init)
        P=E_init.frobenius_polynomial()
        Discr=P.discriminant()
        Trace=-P[1]
        test=True
        for l in L:
            if kronecker_symbol(Discr,l)<>1 or Trace%l==0: test=False
        if test and E_init.is_ordinary:
            V=[]
            for l in L:
                r_1,r_2=P.roots(FiniteField(l))
                v_1=r_1[0]
                v_2=r_2[0]
                V.append((v_1,v_2))
            return E_init,j_init,V
            break
        else:
            continue


# In[15]:

#70% du calcul est occupé par les conversions et substitutions de polynômes
def NormalizedIsogenousWE(j,jprime,A,B,l,Atk_l):
    """Cette fonction prend en argument :
    -j, le j-invariant de la courbe source
    -jprime, le j-invariant de la courbe cible
    -A,B, les coefficients de la courbe initiale
    -Atk_l, le polynôme modulaire d'Atkin de degré l
    et renvoie un couple Aprime, Bprime qui sont les coefficients d'une équation de Weierstrass
        de la courbe image telle que l'isogénie de degré l est normalisée."""
    K=j.parent()
    X,J=Atk_l.parent().gens()
    Pol_1=Atk_l(X,j).univariate_polynomial()
    Pol_2=Atk_l(X,jprime).univariate_polynomial()
    fs=Pol_1.gcd(Pol_2).roots(multiplicities=False)
    if fs==[]:
        raise ValueError, "Curves are not " + l + "-isogenous."
    else:
        f=fs[0]
    #Elkies' formulae
    dX=f*Atk_l.derivative(X)(f,j)
    dJ=j*Atk_l.derivative(J)(f,j)
    dX2=f*Atk_l.derivative(X)(f,jprime)
    dJ2=l*jprime*Atk_l.derivative(J)(f,jprime)
    jj=jprime/(jprime-1728)
    
    Aprime = -K(27)/K(4) * l**4 * (dX2**2 * dJ**2 * B**2) / (dJ2**2 * dX**2 * A**2) * jj
    Bprime = -K(27)/K(4) * l**6 * (dX2**3 * dJ**3 * B**3) / (dJ2**3 * dX**3 * A**3) * jj
    return Aprime,Bprime


# In[16]:

#ne contrôle que la coordonnée x, donc la direction échoue si la trace est nulle
#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728
#On utilise les polynômes modulaires classiques.
#Obsolète, utiliser StepBMSS
def FirstStep(j,A,B,l,Psi_l,Atk_l,v):
    """Cette fonction prend en argument :
    -j, le j-invariant de la courbe initiale
    -A,B, les coefficients de l'équation de Weierstrass de la courbe initiale
    -l, le degré de l'isogénie
    -Psi_l, le polynôme modulaire classique de degré l
    -Atk_l, le polynôme modulaire d'Atkin
    -v, la valeur propre du Frobenius mod l cherchée
    et renvoie un triplet jprime, Aprime, Bprime qui décrit la courbe cible."""
    K=j.parent()
    p=K.cardinality()
    E=EllipticCurve([A,B])
    X_1,X_2=Psi_l.parent().gens()
    pol=Psi_l(j,X_2).univariate_polynomial()
    j_1,j_2=pol.roots(multiplicities=False)
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    try:
        A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l,Atk_l)
        E_1=EllipticCurve([A_1,B_1])
        phi=EllipticCurveIsogeny(E,None,E_1,l)
        K_1=phi.kernel_polynomial()
        Kext=K_1.splitting_field('z')
        t=K_1.any_root(Kext)
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert t**p==f_1(t) #ici t est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        return j_1,A_1,B_1
    except AssertionError:  #ZeroDivisionError?
        A_2,B_2=NormalizedIsogenousWE(j,j_2,A,B,l,Atk_l)
        return j_2,A_2,B_2


# In[1]:

#Les substitutions et conversions de polynômes prennent le plus de temps
def StepBMSS(E,l,Psi_l,Atk_l,v):
    """Cette fonction prend en argument :
    -E, la courbe elliptique initiale
    -l, le degré de l'isogénie
    -Psi_l, le polynôme modulaire classique de degré l
    -Atk_l, le polynôme modulaire d'Atkin
    -v, la valeur propre du Frobenius mod l cherchée
    et renvoie la courbe cible."""
    K=E.base_field()
    p=K.cardinality()
    _,_,_,A,B=E.a_invariants()
    j=E.j_invariant()
    X_1,X_2=Psi_l.parent().gens()
    pol=Psi_l(j,X_2).univariate_polynomial()
    j_1,j_2=pol.roots(multiplicities=False)
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    try:
        A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l,Atk_l)
        E_1=EllipticCurve([A_1,B_1])
        K_1=isogeny_kernel(E,E_1,l)
        Pol_ring=PolynomialRing(K,'X')
        X=Pol_ring.gen()
        Quo_ring=Pol_ring.quotient(K_1)
        Xbar=Quo_ring.gen()
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert Xbar**p==f_1(Xbar) #ici t est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        return E_1
    except AssertionError:  #ZeroDivisionError?
        A_2,B_2=NormalizedIsogenousWE(j,j_2,A,B,l,Atk_l)
        E_2=EllipticCurve([A_2,B_2])
        return E_2


# In[154]:

#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728
def following_step(j,j_prec,A,B,l,Psi_l,Atk_l):
    """Cette fonction prend en argument:
    -j, le j-invariant de la courbe actuelle dans le parcours
    -j_prec, le j-invariant de la courbe précédente
    -A,B, les coefficients de l'équation de Weierstrass actuelle
    -l, le degré considéré
    -Psi_l, le polynôme modulaire classique
    -Atk_l, le polynôme modulaire d'Atkin
    et renvoie un triplet jprime, Aprime, Bprime qui décrit la courbe suivante"""
    X_1,X_2=Psi_l.parent().gens()
    pol=Psi_l(j,X_2).univariate_polynomial()
    X=pol.parent().gen()
    P=pol//(X-j_prec)
    j_1=P.any_root()
    assert j_1<>0 and j_1<>1728
    A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l,Atk_l)
    return j_1,A_1,B_1


# In[155]:

def RouteComputation(j_init,R,L,V,DBC,DBA):
    """Cette fonction prend en argument :
    -j_init, le j-invariant initial
    -R, la liste du nombre de pas (entier relatif) pour chaque nombre premier
    -L, la liste des nombres premiers utilisés
    -V, la liste des couples de valeurs propres du Frobenius mod l, la première donnant le sens positif
    -DBC, le dictionnaire des polynômes modulaires classiques
    -DBA, le dictionnaire des polynômes modulaires d'Atkin
    et renvoie le j-invariant de la courbe finale."""
    E_init = EllipticCurve_from_j(j_init)
    E_init = E_init.short_weierstrass_model()
    _,_,_, A_init, B_init = E_init.a_invariants()
    j_0, A_0, B_0 = j_init, A_init, B_init
    for n in range(len(L)):
        l=L[n]
        v=V[n]
        r=R[n]
        Psi_l=DBC[l]
        Atk_l=DBA[l]
        if r>0:
            j_1, A_1, B_1=first_step(j_0, A_0, B_0, l, Psi_l, Atk_l, v[0])
            for k in range(1,r):
                j_2, A_2, B_2=following_step(j_1, j_0, A_1, B_1, l, Psi_l, Atk_l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        elif r<0:
            j_1, A_1, B_1=first_step(j_0, A_0, B_0, l, Psi_l, Atk_l, v[1])
            for k in range(1,-r):
                j_2, A_2, B_2=following_step(j_1, j_0, A_1, B_1, l, Psi_l, Atk_l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        else:
            pass
    return j_0


# In[159]:

#Calcul du graphe d'isogénies (à utiliser pour p petit)


# In[160]:

def neighbors(j,l,Psi_l):
    """Fonction auxiliaire"""
    j_0,j_1=Psi_l.parent().gens()
    pol=Psi_l.subs(j_0=j).univariate_polynomial()
    assert j<>0 and j<>1728
    j_1,j_2=pol.roots(multiplicities=False)
    return j_1,j_2


# In[161]:

def update(D,j_1,j_2,l):
    """Fonction auxiliaire"""
    if j_1 in D.keys():
        D[j_1][j_2]=l
    else:
        D[j_1]={j_2: l}


# In[162]:

#p<1000 uniquement
def IsogenyGraphComponent(j_0,L,DBC):
    """Cette fonction prend en argument :
    -j_0, le j-invariant de la courbe initiale,
    -L, une liste de nombres premiers Elkies
    -DBC, le dictionnaire des polynômes modulaires classiques
    et renvoie le graphe d'isogénies obtenu.
    Cette fonction ne doit pas être utilisée si le corps de base est grand."""
    Dict={}
    E=EllipticCurve_from_j(j_0)
    assert E.is_ordinary()
    Discr=E.frobenius_polynomial().discriminant()
    for l in L:
        assert kronecker_symbol(Discr,l)==1
    for i in range(len(L)):
        l=L[i]
        Psi_l=DBC[l]
        j_prec=j_0
        j_1,j_2=neighbors(j_0,l,Psi_l)
        update(Dict,j_0,j_1,l)
        j=j_1
        while j<>j_0:
            j_1,j_2=neighbors(j,l,Psi_l)
            if j_1==j_prec : j_1,j_2=j_2,j_1
            update(Dict,j,j_1,l)
            j_prec,j=j,j_1
    G=Graph(Dict,format='dict_of_dicts')
    return G


# In[165]:

#En utilisant les polynômes modulaires d'Atkin


# In[166]:

#Ce code suppose que les polynômes modulaires d'Atkin ont exactement le "bon" nombre de racines, ce qui n'est pas clair
def Atkin_first_step(j,A,B,l,Atk_l,v):
    """Cette fonction prend en argument :
    -j, le j-invariant de la courbe initiale
    -A,B, les coefficients de l'équation de Weierstrass
    -l, le nombre premier utilisé
    -Atk_l, le polynôme modulaire d'Atkin
    -v, la valeur propre du Frobenius mod l cherchée
    et renvoie un triplet jprime, Aprime, Bprime décrivant la courbe cible"""
    K=j.parent()
    p=K.cardinality()
    E=EllipticCurve([A,B])
    F,J=Atk_l.parent().gens()
    f_1,f_2=Atk_l(F,j).univariate_polynomial().roots(multiplicities=False)
    j_1,j_1prime=(Atk_l(f_1,J).univariate_polynomial()).roots(multiplicities=False)
    j_2,j_2prime=(Atk_l(f_2,J).univariate_polynomial()).roots(multiplicities=False)
    if j_1==j: j_1,j_1prime=j_1prime,j_1
    if j_2==j: j_2,j_2prime=j_2prime,j_2
    assert j_1prime==j and j_2prime==j
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    try:
        A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l,Atk_l)
        E_1=EllipticCurve([A_1,B_1])
        phi=EllipticCurveIsogeny(E,None,E_1,l)
        K_1=phi.kernel_polynomial()
        Fext=K_1.splitting_field('z')
        t=K_1.any_root(Fext)
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert t**p==f_1(t) #ici t est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        return j_1,A_1,B_1
    except AssertionError:  #ZeroDivisionError?
        A_2,B_2=NormalizedIsogenousWE(j,j_2,A,B,l,Atk_l)
        return j_2,A_2,B_2


# In[167]:

#Même remarque
def Atkin_following_step(j,j_prec,A,B,l, Atk_l):
    """Cette fonction prend en argument :
    -j, le j-invariant actuel
    -j_prec, le j-invariant précédent
    -A,B, décrivant la courbe actuelle
    -l, le nombre premier utilisé
    -Atk_l, le polynôme d'Atkin
    et renvoie un triplet jprime, Aprime, Bprime décrivant la courbe suivante"""
    F,J=Atk_l.parent().gens()
    f_1,f_2=Atk_l(F,j).univariate_polynomial().roots(multiplicities=False)
    j_1,j_1prime=(Atk_l(f_1,J).univariate_polynomial()).roots(multiplicities=False)
    j_2,j_2prime=(Atk_l(f_2,J).univariate_polynomial()).roots(multiplicities=False)
    if j_1==j: j_1,j_1prime=j_1prime,j_1
    if j_2==j: j_2,j_2prime=j_2prime,j_2
    if j_1==j_prec : j_1,j_2=j_2,j_1
    assert j_2==j_prec and j_1prime==j and j_2prime==j
    assert j_1<>0 and j_1<>1728
    A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l,Atk_l)
    return j_1,A_1,B_1


# In[168]:

def AtkinRouteComputation(j_init,R,L,DBA,V):
    """Cette fonction prend en argument :
    -j_init, le j-invariant initial
    -R, la liste du nombre de pas (entier relatif) pour chaque nombre premier
    -L, la liste des nombres premiers
    -DBA, le dsictionnaire des polynômes d'Atkin
    -V, la liste des couples de valeurs propres du Frobenius mod l, la première donnant le sens positif
    et renvoie le j-invariant de la courbe d'arrivée"""
    E_init = EllipticCurve_from_j(j_init)
    E_init = E_init.short_weierstrass_model()
    _,_,_, A_init, B_init = E_init.a_invariants()
    j_0, A_0, B_0 = j_init, A_init, B_init
    for n in range(len(L)):
        l=L[n]
        v=V[n]
        r=R[n]
        Atk_l=DBA[l]
        if r>0:
            j_1, A_1, B_1=Atkin_first_step(j_0, A_0, B_0, l, Atk_l, v[0])
            for k in range(1,r):
                j_2, A_2, B_2=Atkin_following_step(j_1, j_0, A_1, B_1, l, Atk_l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        elif r<0:
            j_1, A_1, B_1=Atkin_first_step(j_0, A_0, B_0, l, Atk_l, v[1])
            for k in range(1,-r):
                j_2, A_2, B_2=Atkin_following_step(j_1, j_0, A_1, B_1, l, Atk_l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        else:
            pass
    return j_0


# In[169]:

#En utilisant des courbes ayant de la torsion rationnelle


# In[170]:

#A utiliser avec p petit
def FindGoodCurve(L,N,K):
    """Cette fonction prend en argument :
    -L, liste de nombres premiers \neq 2
    -N, nombre d'essais
    -K, corps de base
    et renvoie une courbe elliptique pour laquelle ces nombres premiers sont bons.
    Renvoie None si rien n'est trouvé"""
    p=K.cardinality()
    for k in range(N):
        try:
            j_0=K.random_element()
            E_0=EllipticCurve(j=j_0)
            E_0=E_0.short_weierstrass_model()
            P=E_0.frobenius_polynomial()
            Trace=-P[1]
            Discr=P.discriminant()
            for l in L:
                assert kronecker_symbol(Discr,l)==1 and Trace%l==(p+1)%l #Assure la présence de l-torsion rationnelle
            return E_0
            break
        except AssertionError:
            continue


# In[171]:

def FindGoodPrimes(j_0):
    """Cette fonction prend en argument :
    -j_0, un j-invariant
    et renvoie la liste des nombres premiers \leq 100 bons pour cette courbe"""
    E_0=EllipticCurve(j=j_0)
    p=j_0.parent().cardinality()
    P=E_0.frobenius_polynomial()
    Trace=-P[1]
    Discr=P.discriminant()
    return [l for l in prime_range(100) if (kronecker_symbol(Discr,l)==1 and Trace%l==(p+1)%l)]


# In[172]:

#r=1 ou 2 si p est grand
def FindGoodLength(r,N,K):
    """Cette fonction prend en argument :
    -r, un entier positif
    -N, un nombre d'essais
    -K, un corps fini
    et renvoie E,L,Card où E est une courbe elliptique pour lequel les nombres premiers dans L sont bons,
    tel que len(L)\geq r, et son cardinal"""
    for k in range(N):
        j_0=K.random_element()
        L=FindGoodPrimes(j_0)
        if len(L)<r:
            continue
        else:
            E=EllipticCurve(j=j_0)
            return E, L, E.cardinality()
            break


# In[173]:

#Réécrire la multiplication des points ??
def FindRationalTorsion(E,l,Card):
    """Cette fonction prend en argument :
    -E, une courbe elliptique
    -l, un nombre premier tel que E admet de la l-torsion rationnelle
    -Card, son cardinal
    et renvoie un point rationnel de l-torsion"""
    Cofactor=Card//l
    for k in range(10):
        try:
            P=E.random_point()
            Q=Cofactor*P
            assert not Q.is_zero()
            return Q
            break
        except AssertionError:
            continue


# In[174]:

def TorsionPoints(E,L,Card):
    """Cette fonction prend en argument :
    -E, une courbe elliptique
    -L, une liste de nombres premiers tels que E admet de la torsion rationnelle
    -Card, son cardinal
    et renvoie une liste de points de torsion"""
    return [FindRationalTorsion(E,l,Card) for l in L]


# In[3]:

#99% du calcul est A=K['X']
def SubgroupPolynomial(E,Q,l): #Suppose que E est sous forme de Weierstrass, et Q est un point d'ordre premier l
    """Fonction auxiliaire"""
    K=E.base_field()
    A=K['X']
    X=A.gen()
    pol=A(1)
    Point=Q
    for k in range((l-1)/2):
        (x_p,y_p,z_p)=Point
        assert z_p==1
        pol *= (X-x_p)
        Point += Q
    return pol


# In[4]:

#Obsolète tant que l'on ne réécrit pas les formules pour les applications
def StepWithTorsion(E,L,T,Card,i):
    """Cette fonction prend en argument :
    -E, une courbe elliptique
    -L, la liste des nombres premiers utilisés
    -T, une liste de points de torsion
    -Card, le cardinal de la courbe
    -i, l'indice utilisé
    et renvoie Eprime, Tprime : courbe image et liste de points de torsion"""
    Q=T[i]
    pol=SubgroupPolynomial(E,Q,L[i])
    phi=EllipticCurveIsogeny(E,kernel=pol,degree=L[i])
    Eprime=phi.codomain()
    f,g=phi.rational_maps()
    Tprime=[]
    for k in range(len(L)):
        if k<>i:
            Q_k=T[k]
            x_k,y_k,z_k=Q_k[0],Q_k[1],Q_k[2]
            assert z_k==1
            Q_kprime=Eprime.point([f(x_k,y_k),g(x_k,y_k)])
            Tprime.append(Q_kprime)
        else:
            Qprime=FindRationalTorsion(Eprime,L[i],Card)
            Tprime.append(Qprime)
    return Eprime,Tprime


# In[1]:

#Obsolète tant qu'on ne réécrit pas les formules pour les applications
def StepWithTorsion_x(E,L,T,Card,i):
    """Cette fonction prend en argument :
    -E, une courbe elliptique
    -L, la liste des nombres premiers utilisés
    -T, une liste de points de torsion
    -Card, le cardinal de la courbe
    -i, l'indice utilisé
    et renvoie Eprime, Tprime : courbe image et liste de points de torsion"""
    Q=T[i]
    pol=SubgroupPolynomial(E,Q,L[i])
    phi=EllipticCurveIsogeny(E,kernel=pol,degree=L[i])
    Eprime=phi.codomain()
    f=phi.x_rational_map()
    Tprime=[]
    for k in range(len(L)):
        if k<>i:
            Q_k=T[k]
            x_k,y_k,z_k=Q_k[0],Q_k[1],Q_k[2]
            assert z_k==1
            Q_kprime=Eprime.lift_x(f(x_k))
            Tprime.append(Q_kprime)
        else:
            Qprime=FindRationalTorsion(Eprime,L[i],Card)
            Tprime.append(Qprime)
    return Eprime,Tprime


# In[ ]:

#Formules de Vélu
def ImageCurve(E,P):
    """Cette fonction prend en argument :
    -E, courbe elliptique
    -P, polynôme définissant le noyau d'une isogénie cyclique de degré l impair, séparable et normalisée
    et renvoie la courbe image avec les formules de Velu"""
    a_1, a_2, a_3 , a_4, a_6 = E.a_invariants()
    b_2, b_4, b_6, b_8 = E.b_invariants()
    n = P.degree()
    s_1 = -P[n - 1]
    s_2 = P[n - 2]
    s_3 = -P[n - 3]
    t = 6*(s_1**2 - 2*s_2) + b_2*s_1 + n*b_4
    w = 10*(s_1**3 - 3*s_1*s_2 + 3*s_3) + 2*b_2*(s_1**2 - 2*s_2) + 3*b_4*s_1 + n*b_6
    E1 = EllipticCurve([a_1, a_2, a_3, a_4 - 5*t, a_6 - b_2*t - 7*w])
    return E1


# In[ ]:

#Le plus rapide jusqu'à présent
def StepWithoutRationalMaps(E,L,Card,i):
    """Cette fonction prend en argument :
    -E, une courbe elliptique
    -L, la liste des nombres premiers
    -Card, le cardinal de la courbe
    -i, l'indice utilisé
    et renvoie la courbe image."""
    Q=FindRationalTorsion(E,L[i],Card)
    pol=SubgroupPolynomial(E,Q,L[i])
    E1=ImageCurve(E,pol)
    return E1

