
# coding: utf-8

# In[19]:

p=83
F=FiniteField(p)
L=[3,5]
#Le choix du nombre premier est important : il faut qu'il "accepte" de petits nombres premiers dans L


# In[2]:

#packages
from sage.databases.db_modular_polynomials import ModularPolynomialDatabase


# In[38]:

def SystemDefinition(L):
    #On cherche des données initiales ayant les bonnes propriétés.
    #A éviter : les courbes supersingulières, les j-invariants 0 et 1728, les nombres premiers divisant le discriminant
    #et la trace, les nombres premiers inertes.
    for k in range(50):
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
                r_1,r_2=P.roots(FiniteField(l))
                v_1=r_1[0]
                v_2=r_2[0]
                V.append((v_1,v_2))
            return j_init,V
            break
        else:
            continue
    return 'Failure'


# In[39]:

def get_psi_l(l):
    DBMP=ClassicalModularPolynomialDatabase()
    return DBMP[l]


# In[40]:

def find_scaling(E_init,E_1,l):
    for a in F:
        try:
            assert a<>0
            E_2=E_1.scale_curve(a)
            phi=EllipticCurveIsogeny(E_init,None,E_2,degree=l)
            return E_2,phi
            break
        except: continue


# In[41]:

#ne contrôle que la coordonnée x, donc la direction échoue si la trace est nulle
#pour l'instant le facteur de scaling est cherché de façon exhaustive, il reste à utiliser les formules de Schoof
#pour déterminer le facteur de scaling directement

#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728

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
        E_1,phi=find_scaling(E,E_1,l)
        K_1=phi.kernel_polynomial()
        Fext=K_1.splitting_field('z')
        t=K_1.roots(Fext)[0][0]
        f_1=E.multiplication_by_m(Integer(v),x_only=True)
        assert t**p==f_1(t) #ici t est l'abscisse d'un point de la courbe qui est dans Ker(phi)
        return j_1
    except AssertionError:#ZeroDivisionError?
        E_2=EllipticCurve_from_j(j_2)
        if not E.is_isogenous(E_2): E_2=E_2.quadratic_twist()
        return j_2


# In[42]:

#Comme dit plus haut, on soulève une exception si l'on atteint j=0 ou 1728
def following_step(j,l,j_prec):
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    j1=pol.parent().gen()
    P=pol//(j1-j_prec)
    r_1=P.roots()
    j_1=r_1[0][0]
    assert j_1<>0 and j_1<>1728
    return j_1


# In[43]:

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
            j_1=first_step(j_0,l,v[0])
            for k in range(1,r):
                j_2=following_step(j_1,l,j_0)
                j_0=j_1
                j_1=j_2
            j_0=j_1
        elif r<0:
            j_1=first_step(j_0,l,v[1])
            for k in range(1,r):
                j_2=following_step(j_1,l,j_0)
                j_0=j_1
                j_1=j_2
            j_0=j_1
        else:
            pass
    return j_0


# In[71]:

def CryptosystemParameters(L):
    k=3
    j_init,V=SystemDefinition(L)
    R_priv=[]
    for i in range(len(L)):
        r=ZZ.random_element(-k,k+1)
        R_priv.append(r)
    j_pub=RouteComputation(j_init,R_priv,L,V)
    return j_init,j_pub,k,L,V,R_priv


# In[45]:

def Encrypt(j_pub,m,k,L,V):
    R_enc=[]
    for i in range(len(L)):
        r=ZZ.random_element(-k,k+1)
        R_enc.append(r)
    j_enc=RouteComputation(j_pub,R_enc,L,V)
    s=m*j_enc
    j_add=RouteComputation(j_init,R_enc,L,V)
    return s,j_add


# In[46]:

def Decrypt(s,j_add,L,V,R_priv):
    j_enc=RouteComputation(j_add,R_priv,L,V)
    m=s/j_enc
    return m


# In[64]:

#Calcul du graphe d'isogénies


# In[65]:

def neighbors(j,l):
    pol=get_psi_l(l).subs(j0=j).univariate_polynomial()
    assert j<>0 and j<>1728
    (r_1,r_2)=pol.roots()
    j_1=r_1[0]
    j_2=r_2[0]
    return j_1,j_2


# In[66]:

def update(D,j_1,j_2,l):
    if j_1 in D.keys():
        D[j_1][j_2]=l
    else:
        D[j_1]={j_2: l}


# In[67]:

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
            j_1=following_step(j,l,j_prec)
            update(Dict,j,j_1,l)
            j_prec=j
            j=j_1
    G=Graph(Dict,format='dict_of_dicts')
    return G


# In[68]:

def CompleteIsogenyGraph(L):
    #On trace ici un graphe simple non orienté : on ignore donc les multiplicités pour j=0 et 1728
    #On relie deux j-invariants par une arête labellisée 'l' si les deux courbes sont liées par une isogénie de degré l
    Dict={}
    for j in F:
        Dict[j]={}
    for l in L:
        psi_l=get_psi_l(l)
        for j in F:
            for (j_1,_) in psi_l.subs(j0=j).univariate_polynomial().roots():
                Dict[j][j_1]=l
    G=Graph(Dict,format='dict_of_dicts')
    return G


# In[ ]:



