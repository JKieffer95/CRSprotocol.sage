
# coding: utf-8

# In[1]:

#packages
from sage.databases.db_modular_polynomials import ModularPolynomialDatabase


# In[2]:

p=next_prime(next_prime(2**50))
K=FiniteField(p)
L=[11,23,29,59]
#Le choix du nombre premier est important : il faut qu'il "accepte" de petits nombres premiers dans L
DBMP=ClassicalModularPolynomialDatabase()
DBAP=AtkinModularPolynomialDatabase()


# In[3]:

def SystemDefinition(L):
    #On cherche des données initiales ayant les bonnes propriétés.
    #A éviter : les courbes supersingulières, les j-invariants 0 et 1728, les nombres premiers divisant le discriminant
    #et la trace, les nombres premiers inertes.
    for k in range(50):
        j_init=K.random_element()
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
                r_1,r_2=P.roots(FiniteField(l))
                v_1=r_1[0]
                v_2=r_2[0]
                V.append((v_1,v_2))
            return j_init,V
            break
        else:
            continue
    raise ValueError, "Parameters not found"


# In[4]:

def get_psi_l(l):
    return DBMP[l]


# In[5]:

def get_atk_l(l):
    return DBAP[l]


# In[6]:

def NormalizedIsogenousWE(j,jprime,A,B,l):
    P=PolynomialRing(K,"X,J")
    X,J=P.gens()
    Atk_l=P(get_atk_l(l))
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


# In[7]:

#ne contrôle que la coordonnée x, donc la direction échoue si la trace est nulle

#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728

#On utilise les polynômes modulaires d'Atkin, cette méthode nécessite p\neq 2,3 (?) Cela pose des problèmes pour l grand.

def first_step(j,A,B,l,v):
    E=EllipticCurve([A,B])
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    j_1,j_2=pol.roots(multiplicities=False)
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    try:
        A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l)
        E_1=EllipticCurve([A_1,B_1])
        phi=EllipticCurveIsogeny(E,None,E_1,l)
        K_1=phi.kernel_polynomial()
        Kext=K_1.splitting_field('z')
        t=K_1.roots(Kext,multiplicities=False)[0]
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert t**p==f_1(t) #ici t est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        return j_1,A_1,B_1
    except AssertionError:  #ZeroDivisionError?
        A_2,B_2=NormalizedIsogenousWE(j,j_2,A,B,l)
        return j_2,A_2,B_2


# In[8]:

#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728
def following_step(j,j_prec,A,B,l):
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    j1=pol.parent().gen()
    P=pol//(j1-j_prec)
    r_1=P.roots(multiplicities=False)
    j_1=r_1[0]
    assert j_1<>0 and j_1<>1728
    A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l)
    return j_1,A_1,B_1


# In[9]:

def RouteComputation(j_init,R,L,V):
    #j_init : le j-invariant de la courbe initiale
    #L : la liste de nombres premiers considérés
    #R : la route, i.e. liste du nombre de pas pour chaque nombre premier
    #V : la liste des couples de valeurs propres donnant l'orientation
    E_init = EllipticCurve_from_j(j_init)
    E_init = E_init.short_weierstrass_model()
    _,_,_, A_init, B_init = E_init.a_invariants()
    j_0, A_0, B_0 = j_init, A_init, B_init
    for n in range(len(L)):
        l=L[n]
        v=V[n]
        r=R[n]
        if r>0:
            j_1, A_1, B_1=first_step(j_0, A_0, B_0, l, v[0])
            for k in range(1,r):
                j_2, A_2, B_2=following_step(j_1, j_0, A_1, B_1, l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        elif r<0:
            j_1, A_1, B_1=first_step(j_0, A_0, B_0, l, v[1])
            for k in range(1,-r):
                j_2, A_2, B_2=following_step(j_1, j_0, A_1, B_1, l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        else:
            pass
    return j_0


# In[10]:

def CryptosystemParameters(L):
    k=3
    j_init,V=SystemDefinition(L)
    R_priv=[]
    for i in range(len(L)):
        r=ZZ.random_element(-k,k+1)
        R_priv.append(r)
    j_pub=RouteComputation(j_init,R_priv,L,V)
    return j_init,j_pub,k,L,V,R_priv


# In[11]:

def Encrypt(j_pub,m,k,L,V):
    R_enc=[]
    for i in range(len(L)):
        r=ZZ.random_element(-k,k+1)
        R_enc.append(r)
    j_enc=RouteComputation(j_pub,R_enc,L,V)
    s=m*j_enc
    j_add=RouteComputation(j_init,R_enc,L,V)
    return s,j_add


# In[12]:

def Decrypt(s,j_add,L,V,R_priv):
    j_enc=RouteComputation(j_add,R_priv,L,V)
    m=s/j_enc
    return m


# In[13]:

#Calcul du graphe d'isogénies (à utiliser pour p petit)


# In[14]:

def neighbors(j,l):
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    assert j<>0 and j<>1728
    (r_1,r_2)=pol.roots()
    j_1=r_1[0]
    j_2=r_2[0]
    return j_1,j_2


# In[15]:

def update(D,j_1,j_2,l):
    if j_1 in D.keys():
        D[j_1][j_2]=l
    else:
        D[j_1]={j_2: l}


# In[16]:

def IsogenyGraphComponent(j_0,L):
    #on construit un graphe au format "dict_of_dicts". L est une liste non vide de (petits) premiers totalement scindés 
    #dans \Q(\sqrt(Discr))
    Dict={}
    E=EllipticCurve_from_j(j_0)
    assert E.is_ordinary()
    Discr=E.frobenius_polynomial().discriminant()
    for l in L:
        assert kronecker_symbol(Discr,l)==1
    for l in L:
        j_prec=j_0
        j_1,j_2=neighbors(j_0,l)
        update(Dict,j_0,j_1,l)
        j=j_1
        while j<>j_0:
            j_1,j_2=neighbors(j,l)
            if j_1==j_prec : j_1,j_2=j_2,j_1
            update(Dict,j,j_1,l)
            j_prec,j=j,j_1
    G=Graph(Dict,format='dict_of_dicts')
    return G


# In[17]:

def CompleteIsogenyGraph(L):
    #On trace ici un graphe simple non orienté : on ignore donc les multiplicités pour j=0 et 1728
    #On relie deux j-invariants par une arête labellisée 'l' si les deux courbes sont liées par une isogénie de degré l
    Dict={}
    for j in K:
        Dict[j]={}
    for l in L:
        psi_l=get_psi_l(l)
        for j in F:
            for (j_1,_) in psi_l.subs(j0=j).univariate_polynomial().roots():
                Dict[j][j_1]=l
    G=Graph(Dict,format='dict_of_dicts')
    return G


# In[18]:

#Une meilleure idée serait peut-être de faire agir le groupe de classe de O_D pour déterminer les courbes intéressantes
#à faire apparaître dans le graphe


# In[19]:

#En utilisant les polynômes modulaires d'Atkin


# In[20]:

#Ce code suppose que les polynômes modulaires d'Atkin ont exactement le "bon" nombre de racines, ce qui demande démo
def Atkin_first_step(j,A,B,l,v):
    E=EllipticCurve([A,B])
    Ann=PolynomialRing(K,"F,J")
    F,J=Ann.gens()
    Phi=Ann(get_atk_l(l))
    f_1,f_2=Phi.subs(J=j).univariate_polynomial().roots(multiplicities=False)
    j_1,j_1prime=(Phi.subs(F=f_1).univariate_polynomial()).roots(multiplicities=False)
    j_2,j_2prime=(Phi.subs(F=f_2).univariate_polynomial()).roots(multiplicities=False)
    if j_1==j: j_1,j_1prime=j_1prime,j_1
    if j_2==j: j_2,j_2prime=j_2prime,j_2
    assert j_1prime==j and j_2prime==j
    assert j_1<>0 and j_1<>1728 and j_2<>0 and j_2<>1728
    try:
        A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l)
        E_1=EllipticCurve([A_1,B_1])
        phi=EllipticCurveIsogeny(E,None,E_1,l)
        K_1=phi.kernel_polynomial()
        Fext=K_1.splitting_field('z')
        t=K_1.roots(Fext,multiplicities=False)[0]
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert t**p==f_1(t) #ici t est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        return j_1,A_1,B_1
    except AssertionError:  #ZeroDivisionError?
        A_2,B_2=NormalizedIsogenousWE(j,j_2,A,B,l)
        return j_2,A_2,B_2


# In[21]:

def Atkin_following_step(j,j_prec,A,B,l):
    Ann=PolynomialRing(K,"F,J")
    F,J=Ann.gens()
    Phi=Ann(get_atk_l(l))
    f_1,f_2=Phi.subs(J=j).univariate_polynomial().roots(multiplicities=False)
    j_1,j_1prime=(Phi.subs(F=f_1).univariate_polynomial()).roots(multiplicities=False)
    j_2,j_2prime=(Phi.subs(F=f_2).univariate_polynomial()).roots(multiplicities=False)
    if j_1==j: j_1,j_1prime=j_1prime,j_1
    if j_2==j: j_2,j_2prime=j_2prime,j_2
    if j_1==j_prec : j_1,j_2=j_2,j_1
    assert j_2==j_prec and j_1prime==j and j_2prime==j
    assert j_1<>0 and j_1<>1728
    A_1,B_1=NormalizedIsogenousWE(j,j_1,A,B,l)
    return j_1,A_1,B_1


# In[22]:

def AtkinRouteComputation(j_init,R,L,V):
    #j_init : le j-invariant de la courbe initiale
    #L : la liste de nombres premiers considérés
    #R : la route, i.e. liste du nombre de pas pour chaque nombre premier
    #V : la liste des couples de valeurs propres donnant l'orientation
    E_init = EllipticCurve_from_j(j_init)
    E_init = E_init.short_weierstrass_model()
    _,_,_, A_init, B_init = E_init.a_invariants()
    j_0, A_0, B_0 = j_init, A_init, B_init
    for n in range(len(L)):
        l=L[n]
        v=V[n]
        r=R[n]
        if r>0:
            j_1, A_1, B_1=Atkin_first_step(j_0, A_0, B_0, l, v[0])
            for k in range(1,r):
                j_2, A_2, B_2=Atkin_following_step(j_1, j_0, A_1, B_1, l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        elif r<0:
            j_1, A_1, B_1=Atkin_first_step(j_0, A_0, B_0, l, v[1])
            for k in range(1,-r):
                j_2, A_2, B_2=Atkin_following_step(j_1, j_0, A_1, B_1, l)
                j_0, A_0, B_0 = j_1, A_1, B_1
                j_1, A_1, B_1 = j_2, A_2, B_2
            j_0, A_0, B_0 = j_1, A_1, B_1
        else:
            pass
    return j_0


# In[24]:

#En utilisant des courbes ayant de la torsion rationnelle


# In[118]:

#Paramètres
p=next_prime(10000)
K=FiniteField(p)
L=[5,7,11]


# In[218]:

def FindGoodCurve(L,N):
    for k in range(N):
        try:
            j_0=K.random_element()
            E_0=EllipticCurve_from_j(j_0)
            E_0=E_0.short_weierstrass_model()
            P=E_0.frobenius_polynomial()
            Trace=-P[1]
            Discr=P.discriminant()
            Card=p+1
            for l in L:
                assert kronecker_symbol(Discr,l)==1 and Trace%l==(p+1)%l #Assure la présence de l-torsion rationnelle
            return E_0,Card
            break
        except AssertionError:
            continue


# In[84]:

def FindGoodPrimes(j_0):
    E_0=EllipticCurve_from_j(j_0)
    P=E_0.frobenius_polynomial()
    Trace=-P[1]
    Discr=P.discriminant()
    return [l for l in prime_range(100) if (kronecker_symbol(Discr,l)==1 and Trace%l==(p+1)%l)]


# In[242]:

def FindGoodLength(r,N):
    for k in range(N):
        if k%10000==0: print k
        j=K.random_element()
        L=FindGoodPrimes(j)
        if len(L)<r:
            continue
        else:
            E=EllipticCurve_from_j(j)
            Card=E.cardinality()
            return E,L,Card
            break


# In[217]:

def FindRationalTorsion(E,l,Card):
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


# In[115]:

def TorsionPoints(E,L,Card):
    return [FindRationalTorsion(E,l,Card) for l in L]


# In[309]:

def StepWithTorsion(E,L,T,Card,i):
    Q=T[i]
    phi=EllipticCurveIsogeny(E,kernel=Q,degree=L[i])
    Eprime=phi.codomain()
    f,g=phi.rational_maps()
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


# In[312]:

def StepWithTorsion_x(E,L,T,Card,i):
    Q=T[i]
    phi=EllipticCurveIsogeny(E,kernel=Q,degree=L[i])
    Eprime=phi.codomain()
    f=phi.x_rational_map()
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


# In[349]:

def StepWithoutRationalMaps(E,L,Card,i):
    Q=FindRationalTorsion(E,L[i],Card)
    phi=EllipticCurveIsogeny(E,kernel=Q,degree=L[i])
    return phi.codomain()


# In[183]:

def RouteWithTorsion(E_init,L,T_init,Card,R):
    #R est la liste du nombre de pas à effectuer pour chaque nombre premier, un entier positif
    E,T=E_init,T_init
    for i in range(len(L)):
        for k in range(R[i]):
            E,T=StepWithTorsion(E,L,T,Card,i)
    return E,T


# In[354]:

#Tests
p=next_prime(2**300)
K=FiniteField(p)

