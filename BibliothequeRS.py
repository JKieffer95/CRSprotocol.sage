
# coding: utf-8

# In[ ]:

from sage.all import *
from BMSS import *


# In[159]:

#Calcul du graphe d'isogénies (à utiliser pour p petit)


# In[170]:

#Donnée initiale pour le graphe d'isogénies
def FindCurve(L, N, K):
    
    r"""Arguments :
    
    -L, liste de nombres premiers \neq 2
    -N, nombre d'essais
    -K, corps de base
    
    Résultat :
    
    -E_0, une courbe elliptique
    
    pour laquelle ces nombres premiers sont bons.
    Renvoie None si rien n'est trouvé"""
    
    p = K.cardinality()
    for k in range(N):
        try:
            j_0 = K.random_element()
            E_0 = EllipticCurve(j = j_0)
            E_0 = E_0.short_weierstrass_model()
            P   = E_0.frobenius_polynomial()
            Trace = - P[1]
            Discr = P.discriminant()
            for l in L:
                assert kronecker_symbol(Discr,l) == 1
            return E_0
            break
        except AssertionError:
            continue


# In[160]:

def neighbors(j, l, Psi_l):
    
    r"""Fonction auxiliaire"""
    
    j0, j1 = Psi_l.parent().gens()
    pol = Psi_l.subs(j0 = j).univariate_polynomial()
    assert j<>0 and j<>1728
    j_1, j_2 = pol.roots(multiplicities=False)
    return j_1, j_2


# In[161]:

def update(D, j_1, j_2, l):
    
    r"""Fonction auxiliaire"""
    
    if j_1 in D.keys():
        D[j_1][j_2]=l
    else:
        D[j_1]={j_2: l}


# In[162]:

#p<1000 uniquement
def IsogenyGraph(j_0, L, ModPol):
    
    r"""Arguments :
    
    -E_0, la courbe initiale,
    -L, une liste de nombres premiers Elkies
    -ModPol, la liste des polynômes modulaires correspondants dans le corps
    
    Résultat :
    
    -un graphe G
    
    qui est le graphe d'isogénies obtenu.
    Cette fonction ne doit pas être utilisée si le corps de base est grand."""
    
    Dict = {}
    E_0 = EllipticCurve_from_j(j_0)
    assert E_0.is_ordinary()
    Discr = E_0.frobenius_polynomial().discriminant()
    for l in L:
        assert kronecker_symbol(Discr,l)==1
    for i in range(len(L)):
        l = L[i]
        Psi_l = ModPol[l]
        j_prec = j_0
        j_1, j_2 = neighbors(j_0, l, Psi_l)
        update(Dict, j_0, j_1, l)
        j = j_1
        while j<>j_0:
            j_1, j_2 = neighbors(j, l, Psi_l)
            if j_1 == j_prec :
                j_1, j_2 = j_2, j_1
            update(Dict, j, j_1, l)
            j_prec, j = j, j_1
    G = Graph(Dict, format = 'dict_of_dicts')
    return G


# In[ ]:

#Calcul d'un pas


# In[1]:

def FirstStep(E_0, l, A, P, S, algorithm = 'Modular', kernel_algorithm = 'BMSS', Card = None, v = None, Psi_l = None, Atk_l = None):
    
    r"""Arguments :
    
    - E_0, la courbe elliptique initiale
    - l, le degré de l'isogénie
    - A, un anneau de polynômes univarié sur le corps
    - P, anneau de séries formelles dur le corps
    - S, anneau de séries de Laurent sur le corps
    - algorithm : 'Modular', 'Atkin" ou 'Torsion' (default : 'Modular'). Définit la méthode utilisée 
        pour trouver les voisins
    - kernel_algorithm : 'BMSS' ou 'Stark' (default : 'BMSS'). Définit l'algorithme pour le calcul du noyau 
        (ignoré si algorithm = 'Torsion')
    - (optionnel) Card, le cardinal de E(\F_p)
        doit être donné si algorithm = 'Torsion'
    - (optionnel) v, la valeur propre du Frobenius mod l cherchée 
        doit être donnée si algorithm = 'Modular' ou 'Atkin".
    - (optionnel) Psi_l, le polynôme modulaire classique
        doit être donné si algorithm = 'Modular'
    - (optionnel) Atk_l, le polynôme modulaire d'Atkin
        doit être donné si algorithm = 'Modular' ou 'Atkin'
    
    Résultat :
    
    -E_1, une courbe elliptique
    
    qui est la courbe image cherchée. 
    Renvoie une erreur si on atteint un j-invariant 0 ou 1728"""
    
    #Initial data
    K = E_0.base_field()
    p = K.cardinality()
    _, _, _, A_0, B_0 = E_0.a_invariants()
    j_0 = E_0.j_invariant()
    X = A.gen()
    
    if algorithm == 'Torsion' :
        
        if Card is None :
            raise ValueError, "Cardinal (Card) must be given if algorithm is 'Torsion'"
            
        #Finding an l-torsion rational point
        Q = FindRationalTorsion(E_0, l, Card)
        
        #Computing the kernel polynomial
        Ker_pol = SubgroupPolynomial(l, Q, A)
        
        #Computing the image curve
        E_1 = QuotientCurve(E_0, Ker_pol)
        
        return E_1
    
    elif algorithm == 'Modular' :
    
        if Psi_l is None :
            raise ValueError, "Modular polynomial (Psi_l) must be given if algorithm is 'Modular'"
        if Atk_l is None :
            raise ValueError, "Atkin polynomial (Atk_l) must be given if algorithm is 'Modular'"
        if v is None :
            raise ValueError, "Frobenius eigenvalue (v) must be given if algorithm is 'Modular'"
        
        
        #Computing j-invariants and image curves
        pol = Psi_l(j_0, X)
        j_1, j_2 = pol.roots(multiplicities = False)
        if j_1 == 0 or j_1 == 1728 or j_2 == 0 or j_2 == 1728 :
            raise ValueError, "j-invariant 0 or 1728 reached"
    
        E_1 = ImageCurve(E_0, j_1, Atk_l, A)
        E_2 = ImageCurve(E_0, j_2, Atk_l, A)
    
        #Computing the isogeny kernel for j_1
        K_1 = isogeny_kernel(E_0, E_1, l, A, P, S, kernel_algorithm)
        Quo_ring = A.quotient(K_1)
        Xbar = Quo_ring.gen() 
            #ici Xbar est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        f_1 = E_0.multiplication_by_m(Integer(v), x_only=True)
        
        #Checking direction : alternative test if l = 3
        if l <> 3 :
            if Xbar**p == f_1(Xbar) :
                return E_1
            else :
                return E_2
        else :
            x_tors = K_1.any_root()
            try :
                E_0.lift_x(x_tors)
                return E_1
            except ValueError :
                return E_2
            
        
    elif algorithm == 'Atkin' :
        
        if Atk_l is None :
            raise ValueError, "Atkin polynomial (Atk_l) must be given if algorithm is 'Atkin'"
        if v is None :
            raise ValueError, "Frobenius eigenvalue (v) must be given if algorithm is 'Atkin'"
        
        #Computing j-invariants and image curves
        f_1, f_2 = Atk_l(X, j_0).roots(multiplicities = False)
        j_1, j_1prime = Atk_l(f_1, X).roots(multiplicities = False)
        j_2, j_2prime = Atk_l(f_2, X).roots(multiplicities = False)
        
        if j_1 == j_0 : 
            j_1 = j_1prime
        if j_2 == j_0 : 
            j_2 = j_2prime
            
        E_1 = ImageCurve(E_0, j_1, Atk_l, A, f_in = f_1)
        E_2 = ImageCurve(E_0, j_2, Atk_l, A, f_in = f_2)
        
        #Computing the isogeny kernel for j_1
        K_1 = isogeny_kernel(E_0, E_1, l, A, P, S)
        Quo_ring = A.quotient(K_1)
        Xbar = Quo_ring.gen() #ici Xbar est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        f_1 = E_0.multiplication_by_m(Integer(v), x_only=True)
        
        #Checking direction
        if l <> 3 :
            if Xbar**p == f_1(Xbar) :
                return E_1
            else :
                return E_2
        else :
            x_tors = K_1.any_root()
            try :
                E_0.lift_x(x_tors)
                return E_1
            except ValueError :
                return E_2
        
    else :
        raise ValueError, "Unknown algorithm. Use 'Modular', 'Atkin' or 'Torsion'"


# In[15]:

def ImageCurve(E_0, j_1, Atk_l, A, f_in = None):
    
    r"""Arguments :
    
    - E_0, la courbe elliptique de départ,
    - j_1, le j-invariant cible
    - Atk_l, le polynôme modulaire d'Atkin de degré l dans le corps
    - A, un anneau de polynômes à une variable sur le corps
    - (optionnel) f_in : un élément du corps vérifiant Atk_l(f, j_0) = Atk_l(f, j_1) = 0
    
    Résultat :
    
    - la courbe image E_1
    
    telle que l'isogénie de degré l est normalisée.
    Renvoie une exception ValueError s'il n'existe pas de telle isogénie"""
    
    #Initial data
    K = E_0.base_field()
    F,J = Atk_l.parent().gens()
    X = A.gen()
    j_0 = E_0.j_invariant()
    l = Atk_l.degree() - 1
    _, _, _, A_0, B_0 = E_0.a_invariants()
    
    #Finding f
    if f_in is not None :
        if Atk_l(f_in, j_0) <> 0 or Atk_l(f_in, j_1) <> 0 :
            raise ValueError, "f_in is not a root of the Atkin polynomial"
        f = f_in

    else :
        Pol_1 = Atk_l(X, j_0)
        Pol_2 = Atk_l(X, j_1)
        fs = Pol_1.gcd(Pol_2).roots(multiplicities=False)
        if fs == []:
            raise ValueError, "Curves are not " + l + "-isogenous."
        else:
            f = fs[0]

    #Elkies' formulae
    dF = f * Atk_l.derivative(F)(f, j_0)
    dJ = j_0 * Atk_l.derivative(J)(f, j_0)
    dF2 = f * Atk_l.derivative(F)(f, j_1)
    dJ2 = l * j_1 * Atk_l.derivative(J)(f, j_1)
    jj = j_1 / (j_1 - 1728)
    
    A_1 = - K(27)/K(4) * l**4 * (dF2**2 * dJ**2 * B_0**2) / (dJ2**2 * dF**2 * A_0**2) * jj
    B_1 = - K(27)/K(4) * l**6 * (dF2**3 * dJ**3 * B_0**3) / (dJ2**3 * dF**3 * A_0**3) * jj
    
    return EllipticCurve([A_1, B_1])


# In[173]:

def FindRationalTorsion(E, l, Card):
    
    r"""Arguments :
    
    -E, une courbe elliptique
    -l, un nombre premier
    -Card, son cardinal
    
    et renvoie un point rationnel de l-torsion.
    Renvoie une erreur si E n'a pas de l-torsion rationnelle"""
    
    Cofactor=Card//l
    
    P=E.random_point()
    Q=Cofactor*P
    
    #Q may be zero
    while Q.is_zero():
        P=E.random_point()
        Q=Cofactor*P
    
    if l*Q <> 0 :
        raise ValueError, "Elliptic Curve has no rational l-torsion"
    
    return Q


# In[3]:

def SubgroupPolynomial(l, Q, A):
    
    r"""Arguments :
    
    - l, un nombre premier
    - Q, un point de l-torsion sur une courbe elliptique sous forme de Weierstrass réduite
    - A, un anneau de polynômes sur le corps
    
    Résultat :
    
    - un polynôme univarié définissant le sous-groupe engendré par Q."""
    
    X = A.gen()
    pol = A(1)
    Point = Q
    
    for k in range( (l-1)/2 ) :
        (x_p, y_p, z_p) = Point
        assert z_p == 1
        pol *= (X - x_p)
        Point += Q
    
    return pol


# In[ ]:

def QuotientCurve(E, P):
    
    r"""Arguments :
    
    -E_0, une courbe elliptique
    -P, polynôme définissant le noyau d'une isogénie cyclique de degré l impair, séparable et normalisée
    
    Résultat :
    
    -la courbe elliptique quotient donnée par les formules de Vélu"""
    
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

#Calcul d'une action complète


# In[154]:

def FollowingStep(E_0, E_prev, A, algorithm, Atk_l, Psi_l = None):
    
    r"""Arguments:
    
    - E_0, la courbe actuelle dans le parcours
    - E_prev, la courbe précédente
    - A, un anneau de polynômes univarié sur le corps
    - algorithm : 'Modular' ou 'Atkin'. Définit le polynôme utilisé
    - Atk_l, le polynôme modulaire d'Atkin
    - (optionnel) Psi_l, le polynôme modulaire classique
        doit être donné si algorithm = 'Modular'
        
    Résultat :
    
    -E_1, une courbe elliptique
    
    qui est la courbe image par l'isogénie suivante.
    Renvoie une erreur si on atteint j=0 ou 1728."""
    
    #Initial data
    X = A.gen()
    j_0 = E_0.j_invariant()
    j_prev = E_prev.j_invariant()
    
    if algorithm == 'Modular' :
        
        if Psi_l is None :
            raise ValueError, "Modular polynomial (Psi_l) must be given if algorithm is 'Modular'"
        
        #Computing the following j-invariant
        pol = Psi_l(j_0, X)
        P = pol // (X-j_prec)
        j_1 = P.any_root()
        if j_1 == 0 or j_1 == 1728 :
            raise ValueError, "j-invariant 0 or 1728 reached"
    
        #Computing the image curve
        E_1 = ImageCurve(E_0, j_1, Atk_l, A)
        
        return E_1
    
    elif algorithm == 'Atkin' :
        
        #Computing the following j-invariant
        f_1, f_2 = Atk_l(X, j_0).roots(multiplicities = False)
        j_1, j_1prime = Atk_l(f_1, X).roots(multiplicities = False)
        j_2, j_2prime = Atk_l(f_2, X).roots(multiplicities = False)
        
        if j_1 == j_0 :
            j_1 = j_1prime
        if j_2 == j_0 :
            j_2 = j_2prime
        if j_1 == j_prev :
            j_1 = j_2
            f_1 = f_2
            
        if j_1 == 0 or j_1 == 1728 :
            raise ValueError, "j-invariant 0 or 1728 reached"
        
        #Computing the image curve
        E_1 = ImageCurve(E_0, j_1, Atk_l, A, f_in = f_1)
        
        return E_1
    
    else :
        raise ValueError, "Unknown algorithm. Use 'Modular' (default) or 'Atkin'"


# In[ ]:

def SeveralSteps(E_init, n, A, P, S, algorithm = 'Modular', Card = None, v = None, Psi_l = None, Atk_l = None):
    
    r"""Arguments :
    
    - E_init, la courbe elliptique initiale
    - n, nombre de pas (entier positif)
    - A, un anneau de polynômes univarié sur le corps
    - P, anneau de séries formelles dur le corps
    - S, anneau de séries de Laurent sur le corps
    - algorithm : 'Modular' (default), 'Atkin' ou 'Torsion'
    - (optionnel) Card : le cardinal de E_init sur \F_p
        doit être donné si algorithm = 'Torsion'
    - (optionnel) v, la valeur propre du Frobenius mod l cherchée
        doit être donné si algorithm = 'Atkin' ou 'Modular'
    - (optionnel) Psi_l, le polynôme modulaire classique
        doit être donné si algorithm = 'Modular'
    - (optionnel) Atk_l, le polynôme modulaire d'Atkin
        doit être donné si algorithm = 'Atkin' ou 'Modular'
    
    Résultat :
    
    -E_fin, une courbe elliptique
    
    qui est la courbe atteinte après n pas dans la direction v"""
    
    E_0 = E_init
    
    #Do nothing if n=0
    if n == 0 :
        return E_0
    
    else : 
        
        if algorithm == 'Torsion' :
            
            for i in range(n) :
                E_0 = FirstStep(E_0, l, A, P, S, algorithm = 'Torsion', Card = Card)
            return E_0
        
        elif algorithm == 'Modular' :
            
            E_1 = FirstStep(E_0, l, A, P, S, algorithm = 'Modular', v = v, Atk_l = Atk_l, Psi_l = Psi_l)
            
            for i in range (n-1):
                E_2 = FollowingStep(E_1, E_0, A, algorithm = 'Modular', Atk_l = Atk_l, Psi_l = Psi_l)
                E_0, E_1 = E_1, E_2
            return E_1
        
        elif algorithm == 'Atkin' :
            
            E_1 = FirstStep(E_0, l, A, P, S, algorithm = 'Atkin', v = v, Atk_l = Atk_l)
            
            for i in range (n-1):
                E_2 = FollowingStep(E_1, E_0, A, algorithm = 'Atkin', Atk_l = Atk_l)
                E_0, E_1 = E_1, E_2
            return E_1
    
        else :
            raise ValueError, "Unknown algorithm. Use 'Modular' (default), 'Atkin' or 'Torsion'"


# In[155]:

def RouteComputation(E_init, R, A, P, S, algorithm = 'Modular', Card = None, V = None, Psi = None, Atk = None):
    
    r"""Arguments :
    
    - E_init, la courbe initiale
    - L, la liste des nombres premiers utilisés
    - A, un anneau de polynômes univarié sur le corps
    - P, anneau de séries formelles dur le corps
    - S, anneau de séries de Laurent sur le corps
    - R, la liste du nombre de pas (entier positif) pour chaque nombre premier
    - V, la liste des valeurs propres du Frobenius mod l donnant le sens positif
    - Psi, la liste des polynômes modulaires classiques
    - Atk, la liste des polynômes modulaires d'Atkin
    - A, un anneau de polynômes univarié
    
    Résultat :
    
    -E_f, une courbe elliptique
    
    qui est la courbe finale atteinte par le parcours."""

    for n in range(len(R)):
        
        r=R[n]
        
        if algorithm == 'Torsion' :
            
            E_f = SeveralSteps(E_init, r, A, P, S, algorithm = 'Torsion', Card = Card)
            
        elif algorithm == 'Modular' :
            
            E_f = SeveralSteps(E_init, r, A, P, S, algorithm = 'Modular', v = V[n], Psi_l = Psi[n], Atk_l = Atk[n])
        
        elif algorithm == 'Atkin' :
            
            E_f = SeveralSteps(E_init, r, A, P, S, algorithm = 'Atkin', v = V[n], Atk_l = Atk[n])
    
    return E_f


# In[ ]:

#Recherche d'une bonne courbe avec de la torsion


# In[171]:

def FindGoodPrimes(E_0, B):
		
	r"""Arguments :
		
	- E_0, une courbe elliptique sur \F_p
		
	Résultat :
		
	- la liste des nombres premiers \leq 100 bons pour cette courbe"""
		
	p = E_0.base_field().cardinality()
	Pol = E_0.frobenius_polynomial()
	Trace = -Pol[1]
	Discr = Pol.discriminant()
	L = []
	for l in prime_range(B):
		A = PolynomialRing(GF(l), "X")
		polmod = A(Pol)
		r = polmod.roots(multiplicities = False)
		if len(r) == 2:
			r1, r2 = r[0], r[1]
			o1, o2 = r1.multiplicative_order(), r2.multiplicative_order()
			order = min(o1, o2)
			if order % 4 == 2:
				order = order/2
			if o1 != o2:
				L.append((l, "order " + `order`))
			else:
				L.append((l, "Elkies"))
	return L


# In[172]:

#r=1 ou 2 si p est grand
def FindGoodLength(r, N, K):
    
    r"""Arguments :
    
    -r, un entier positif
    -N, un nombre d'essais
    -K, un corps fini
    
    Résultat :
    - E_0, L, Card 
    
    où E est une courbe elliptique pour lequel les nombres premiers dans L sont bons,
    tel que len(L)\geq r, et son cardinal"""
    
    for k in range(N):
        
        j_0 = K.random_element()
        E_0 = EllipticCurve(j = j_0)
        L = FindGoodPrimes(E_0)
        
        
        if len(L)<r:
            continue
            
        else:
            return E_0, L, E_0.cardinality()
            break


# In[ ]:

#Fonctions à réécrire


# In[4]:

#Obsolète tant que l'on ne réécrit pas les formules pour les applications
def StepWithTorsion(E,L,T,Card,i):
    r"""Cette fonction prend en argument :
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
    r"""Cette fonction prend en argument :
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

