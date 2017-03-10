
# coding: utf-8

# In[1]:

#packages
from sage.databases.db_modular_polynomials import ModularPolynomialDatabase


# In[4]:

#paramètres globaux
p=83
F=FiniteField(p)
l=3
DBMP=ClassicalModularPolynomialDatabase()
FpXY.<X,Y>=F[]
Phi_l=FpXY(DBMP[l])
Phi_X=Phi_l.derivative(X)
Phi_Y=Phi_l.derivative(Y)
Phi_XX=Phi_X.derivative(X)
Phi_YY=Phi_X.derivative(Y)
Phi_XY=Phi_X.derivative(Y)


# In[6]:

def IsogenousWeierstrassEquation(j,jprime,A,B):
    assert Phi_l(j,jprime)==0
    jtilde=-F(18/l)*(B/A)*(Phi_X(j,jprime)/Phi_Y(j,jprime))*j
    Aprime=-F(1/48)*(jtilde**2)/(jprime*(jprime-1728))
    Bprime=-F(1/864)*(jtilde**3)/((jprime**2)*(jprime-1728))
    return Aprime,Bprime


# In[42]:

#On obtient une équation de la bonne courbe elliptique, mais l'isogénie n'est toujours pas normalisée
A=F(1)
B=F(3)
E=EllipticCurve([A,B])
j=E.j_invariant()
P=Phi_l.subs(Y=j).univariate_polynomial()
jprime=P.roots()[0][0]
Aprime,Bprime=IsogenousWeierstrassEquation(j,jprime,A,B)
Eprime=EllipticCurve([Aprime,Bprime])
Eprime.is_isogenous(E)
#phi=EllipticCurveIsogeny(E,None,Eprime,l)


# In[8]:

#Dans l'algorithme de cryptage, on n'a besoin que du polynôme définissant le noyau : on peut l'obtenir directement
#avec les formules de Schoof


# In[22]:

def compute_p_1(j,jtilde,A,B):
    E_4=-F(48)*A
    E_6=-F(864)*B
    a_1=E_6/E_4
    a_2=E_4**2/E_6
    dj=-a_1*j
    djtilde=-dj*Phi_X(j,jtilde)/(l*Phi_Y(j,jtilde))
    a_1tilde=-djtilde/jtilde
    #a_1tilde est E_6tilde/E_4tilde
    a_2tilde=-djtilde/(jtilde-1728)
    #a_2tilde est E_4tilde**2/E_6tilde
    C_1=-((dj**2)*Phi_XX(j,jtilde)+2*l*dj*djtilde*Phi_XY(j,jtilde)+(l**2)*(djtilde**2)*Phi_YY(j,jtilde))/(jtilde*Phi_X(j,jtilde))
    #C_1 est d2j/dj-l*d2jtilde/djtilde
    C_2=6*(C_1+F(1/2)*a_2+F(2/3)*a_1-F(l/2)*a_2tilde-F(2*l/3)*a_1tilde)
    #C_2 est E_2-l*E_2tilde
    p_1=F(1/12)*F(l)*C_2
    return p_1


# In[40]:

def compute_c_k(A,B):
    L=[]
    
    
    
    return


# In[ ]:

#Le calcul du polynôme définissant le noyau par les formules de Schoof fait intervenir des séries entières.


# In[ ]:




# In[21]:

#déboguage
A=F(1)
B=F(3)
E=EllipticCurve([A,B])
j=E.j_invariant()
phi=Phi_l.subs(Y=j).univariate_polynomial()
jtilde=phi.roots()[0][0]
Aprime,Bprime=IsogenousWeierstrassEquation(j,jtilde,A,B)
p_1,a_1tilde=compute_p_1(j,jtilde,A,B)
E_4tilde=-F(48)*Aprime
E_6tilde=-F(864)*Bprime
a_1tilde,E_6tilde/E_4tilde


# In[ ]:



