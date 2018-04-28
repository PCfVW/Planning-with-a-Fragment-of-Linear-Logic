/* csll
/*****************************************************************************/
/* Tentative de programmation en PROLOG du calcul des sequents pour le       */
/* fragment de la logique lineaire formalisant la planification de type      */
/* STRIPS.                                                                   */
/*                                                            [Eric JACOPIN] */
/*---------------------------------------------------------------------------*/
/* Date de creation      : 06 Octobre  1992                                  */
/* Derniere modification : 30 Mai      1993                                  */
/*****************************************************************************/
/* Premiere version disponible : 0.99 le 15 Octobre 1992                     */

/*****************************************************************************/
/* Quelques outils de mise en oeuvre :                                       */
/*  - time/2              Mesure le temps pris pour prouver un but (O'keefe) */
/*  - space/0               Mesure l'espace de recherche pour trouver un but */
/*  - membre/2                    Teste si un element appartient a une liste */
/*  - conc/3                   Concatenation de deux listes en une troisieme */
/*  - delete/3                              Efface un element dans une liste */
/*  - set_cardinal/2                       Calcule le cardinal d'un ensemble */
/*  - set_difference/3                 Efface un sous-ensemble d'un ensemble */
/*  - set_intersection/3            Calcule l'intersection de deux ensembles */
/*  - set_subset/2         Teste si son 1er parametre est inclus dans le 2nd */
/*  - gensym/3             Creer un nom a partir d'une racine et d'un nombre */
/*  - trans/2              Transforme un nombre en liste des positions ascii */
/*  - genname                          Creer un nom en avec deux autres noms */
/*****************************************************************************/
time(Goal,Duration) :-
   Start is cputime,
   (call(Goal) -> true ; true),
   Duration is cputime - Start.

space :-
   used(N),succ(N,M),
   retract(used(N)),
   assert(used(M)).

membre(X,[X|_]).
membre(X,[_|L]) :- membre(X,L).

conc([],L,L).
conc([X | L1],L2,[X | L3]) :- conc(L1,L2,L3).

del(X,[X|Q],Q).
del(X,[Y|Q],[Y|Q1]) :-
   del(X,Q,Q1).

set_cardinal([],0).
set_cardinal([Head|Tail],M) :-
   set_cardinal(Tail,N),
   M is N + 1.

set_difference([],_,[]).
set_difference([Head|Tail],Set2,Difference) :-
   membre(Head,Set2),
   set_difference(Tail,Set2,Difference).
set_difference([Head|Tail],Set2,[Head|Difference]) :-
   \+(membre(Head,Set2)),
   set_difference(Tail,Set2,Difference).

set_intersection([],_,[]).
set_intersection([Head|Tail],Set2,[Head|Intersection]) :-
   membre(Head,Set2),
   set_intersection(Tail,Set2,Intersection).
set_intersection([Head|Tail],Set2,Intersection) :-
   \+(membre(Head,Set2)),
   set_intersection(Tail,Set2,Intersection).

set_subset([],_).
set_subset([Head|Tail],Set) :-
   membre(Head,Set),
   set_subset(Tail,Set).

set_included([],_).
set_included([Head|Tail],Set) :-
   membre(Head,Set),
   del(Head,Set,Set_sans_Head),
   set_included(Tail,Set_sans_Head).

/* gensym/3                                                        */
/* Permet de Generer un nouveau nom a partir du nom d'un operateur */
/* gensym(Nom_genere,puton,45). --> Nom_genere = puton45           */
gensym(Nom_genere,Nom_operateur,Nombre) :-
   name(Nom_operateur,L1),
   trans(Nombre,Liste),
   conc(L1,Liste,L),
   name(Nom_genere,L).

/* trans/2                                                    */
/* Pour transformer un nombre en la liste des positions ascii */
/* trans(1,L).   --> L = [49].                                */
/* trans(159,L). --> L = [57,53,49].                          */
trans(0,[]).
trans(N,L1) :- 
   Chiffre is 48 + (N mod 10),M is N / 10,
   conc(L,[Chiffre],L1),trans(M,L),!.

/* genname/3                           */
/* genname(un,deux,R). --> undeux.     */
genname(Nom_sequent1,Nom_sequent2,Nom_resultat) :-
   name(Nom_sequent1,L1),
   name(Nom_sequent2,L2),
   conc(L1,L2,L3),
   name(Nom_resultat,L3).

/*****************************************************************************/
/* Un sequent est ici code sous la forme :                                   */
/*                                                                           */
/*         sequent(nom,liaisons,antecedent,consequent)                       */
/*                                                                           */
/* ou "nom" est le nom du sequent (i.e. un atome), "antecedent" et "conse-   */
/* quent" sont deux listes prolog. Par exemple : sequent(axiome,[],[A],[A])  */
/* est le sequent identite.                                                  */
/*****************************************************************************/
/*                                                                           */
/*                                                                           */
/*                                                                           */
/*****************************************************************************/
/* Clauses pour le fragment multiplicatif de la logique lineaire permettant  */
/* la planification de type Strips :                                         */
/*   - g_otimes/2                                                            */
/*   - d_otimes/3                                                            */
/*   - coupure/3                                                             */
/*   - axiome/2                                                              */
/*===========================================================================*/
/* g_otimes/2                                                                */
/* Introduction de la conjonction multiplicative dans l'antecedant d'un      */
/* sequent. La regle d'introduction est :                                    */
/*                                                                           */
/*                     G,A,B |- D                                            */
/*                    ------------                                           */
/*                     G,A*B |- D                                            */
/*                                                                           */
/* Ou A et B sont des formules. Les quatres formats possibles pour A et B    */
/* sont (A1 est l'antecedent du sequent avant l'introduction de * et A2 est  */
/* l'antecedent avec *) :                                                    */
/*                                                                           */
/*        A2                          A1                                     */
/*                                                                           */
/* cas 1  {otimes([A,B])}             {A,B}                                  */
/* cas 2  {Gamma,otimes([A,B])}       {Gamma,A,B},                           */
/* cas 3  {otimes([A | L])}           {A,otimes(L)}                          */
/* cas 4  {Gamma,otimes([A | L])}     {Gamma,A,otimes([L])}                  */
/*                                                                           */
/* Bien evidemment, on peut construire G,A,B |- D a partir de G,A*B |- D et  */
/* vice-versa.                                                               */
/*---------------------------------------------------------------------------*/

/* cas 1 ou 2  A1 = (A2 \ {otimes([A,B])}) U {A,B}                           */
/* cas 1 ou 2  A2 = (A1 \ {A,B}) U {otimes([A,B])}                           */
g_otimes(s(N1,Liaisons,A1,Delta),s(N2,Liaisons,A2,Delta)) :-
   nl,nl,write('Tentative de conjonction multiplicative a gauche (cas 1)'),
   (var(N1) -> /* A1 <--- A2 */
      (membre(otimes([A,B]),A2),
       del(otimes([A,B]),A2,A2_sans_otimes),
       conc([A,B],A2_sans_otimes,A1),
       genname(g_otimes,N2,N1),
       nl,write('   Elimination reussie...'),
       nl,write('   A1 :'),write(s(N1,Liaisons,A1,Delta)),
       nl,write('   A2 :'),write(s(N2,Liaisons,A2,Delta))
      );       /* A1 ---> A2 */
      (\+(membre(otimes(_),A1)),
       membre(A,A1),del(A,A1,L1),
       membre(B,L1),del(B,L1,L2),
       conc([otimes([A,B])],L2,A2),
       genname(g_otimes,N1,N2),
       nl,write('   Introduction reussie...'),
       nl,write('   A1 :'),write(s(N1,Liaisons,A1,Delta)),
       nl,write('   A2 :'),write(s(N2,Liaisons,A2,Delta))
      )),!.
  
/* cas 3 ou 4  A1 = (A2 \ {otimes([A | L])}) U {A,otimes([L])}               */
/* cas 3 ou 4  A2 = (A1 \ {A}) U {otimes([A | L])}                           */
g_otimes(s(N1,Liaisons,A1,Delta),s(N2,Liaisons,A2,Delta)) :-
   nl,write('Tentative de conjonction multiplicative a gauche (cas 2)'),
   (var(N1) -> /* A1 <--- A2 */
      (membre(otimes(L),A2),
       set_cardinal(L,N),N > 2,
       membre(A,L),
       del(A,L,L1),
       del(otimes(L),A2,L2),
       conc([A,otimes(L1)],L2,A1),
       genname(g_otimes,N2,N1),
       nl,write('   Elimination reussie...'),
       nl,write('   A1 :'),write(s(N1,Liaisons,A1,Delta)),
       nl,write('   A2 :'),write(s(N2,Liaisons,A2,Delta))
      );       /* A1 ---> A2 */
      (membre(otimes(L),A1),
       set_cardinal(L,M),M > 1,
       del(otimes(L),A1,A1_sans_otimes),
       membre(A,A1_sans_otimes),
       conc([A],L,L2),
       del(A,A1_sans_otimes,L3),
       conc([otimes(L2)],L3,A2),
       genname(g_otimes,N1,N2),
       nl,write('   Introduction reussie...'),
       nl,write('   A1 :'),write(s(N1,Liaisons,A1,Delta)),
       nl,write('   A2 :'),write(s(N2,Liaisons,A2,Delta))
      )).

/*===========================================================================*/
/* d_otimes/3                                                                */
/* Introduction de la conjonction multiplicative dans le consequent d'un     */
/* sequent. La regle d'introduction est :                                    */
/*                                                                           */
/*                   G |- A,D    G' |- B,D'                                  */
/*                  ------------------------                                 */
/*                       G,G' |- A*B,D,D'                                    */
/*                                                                           */
/* Ou A et B sont des formules. Les 4 cas possibles pour A et B sont (L, L1, */
/* L2, sont des listes) :                                                    */
/*                                                                           */
/*         A           B          A*B                                        */
/*                                                                           */
/* cas 1 : F           G          otimes([F,G])                              */
/* cas 2 : F           otimes(L)  otimes([F | L])                Card(L) > 1 */
/* cas 3 : otimes(L)   H          otimes([H | L])                Card(L) > 1 */
/* cas 4 : otimes(L1)  otimes(L2) otimes([L1 | L2]) Card(L1) et Card(L2) > 1 */
/*                                                                           */
/* On note : A1 = G |- A,D ; A2 = G' |- B,D' ; A3 = G,G' |- A*B,D,D'.        */
/* On considere que A1 est toujours une donnee. Ainsi, la creation d'un nou- */
/* veau sequent peut se faire dans les sens suivants :                       */
/*                                                                           */
/*    CAS 1 :   A1 et A2 ---> A3                                             */
/*    CAS 2 :   A1 et A3 ---> A2                                             */
/*---------------------------------------------------------------------------*/
/* cas 1   A = F et B = G et A*B = otimes([F,G])                             */
d_otimes(s(N1,L1,Av1,Ap1),s(N2,L2,Av2,Ap2),s(N3,L3,Av3,Ap3)) :-
   nl,nl,write('Tentative de conjonction multiplicative a droite (cas 1)'),
   (var(N2) -> /* CAS 2 : A1 et A3 ---> A2 */
      (membre(otimes(L),Ap3),set_cardinal(L,2),
       del(otimes(L),Ap3,Ap3_sans_otimes),
       membre(A,L),membre(A,Ap1),
       del(A,Ap1,Ap1_sans_A),del(A,L,[B]),
       set_difference(Ap3_sans_otimes,Ap1_sans_A,Ap2_sans_B),
       conc([B],Ap2_sans_B,Ap2),
       set_difference(Av3,Av1,Av2),
       genname(N1,N3,N2),
       nl,write('   Elimination reussie...'),
       nl,write('   A1 : '),write(s(N1,L1,Av1,Ap1)),
       nl,write('   A3 : '),write(s(N3,L3,Av3,Ap3)),
       nl,write('   A2 : '),write(s(N2,L2,Av2,Ap2))
      );       /* CAS 1 : A1 et A2 ---> A3 */
      (\+(membre(otimes(_),Ap1)),\+(membre(otimes(_),Ap2)),
       membre(A,Ap1),del(A,Ap1,Ap1_sans_A),
       membre(B,Ap2),del(B,Ap2,Ap2_sans_B),
       conc(Ap1_sans_A,Ap2_sans_B,Ap3_sans_otimes),
       conc(otimes([A,B]),Ap3_sans_otimes,Ap3),
       conc(Av1,Av2,Av3),
       genname(N1,N2,N3)
      )),!.

/* cas 2 : A = F et B = otimes(L) et A*B = otimes([F | L])       Card(L) > 1 */
d_otimes(s(N1,L1,Av1,Ap1),s(N2,L2,Av2,Ap2),s(N3,L3,Av3,Ap3)) :-
   nl,write('Tentative de conjonction multiplicative a droite (cas 2)'),
   (var(N2) -> /* CAS 2 : A1 et A3 ---> A2 */
      (membre(otimes(L),Ap3),set_cardinal(L,Card),Card > 2,
       del(otimes(L),Ap3,Ap3_sans_otimes),
       membre(A,L),membre(A,Ap1),del(A,Ap1,Ap1_sans_A),
       del(A,L,L_sans_A),
       set_difference(Ap3_sans_otimes,Ap1_sans_A,Ap2_sans_otimes),
       conc([otimes(L_sans_A)],Ap2_sans_otimes,Ap2),
       set_difference(Av3,Av1,Av2),
       genname(N1,N3,N2),
       nl,write('   Elimination reussie...'),
       nl,write('   A1 : '),write(s(N1,L1,Av1,Ap1)),
       nl,write('   A3 : '),write(s(N3,L3,Av3,Ap3)),
       nl,write('   A2 : '),write(s(N2,L2,Av2,Ap2))
      );       /* CAS 1 : A1 et A2 ---> A3 */
      (\+(membre(otimes(_),Ap1)),membre(otimes(L),Ap2),
       membre(A,Ap1),del(A,Ap1,Ap1_sans_A),
       del(otimes(L),Ap2,Ap2_sans_otimes),
       conc([A],L,A_otimes_L),
       conc([otimes(A_otimes_L)],Ap1_sans_A,Ap3_sans_Ap2_sans_otimes),
       conc(Ap3_sans_Ap2_sans_otimes,Ap2_sans_otimes,Ap3),
       conc(Av1,Av2,Av3),
       genname(N1,N2,N3)
      )),!.

/* cas 3 : A = otimes(L) et B = H et A*B = otimes([H | L])       Card(L) > 1 */
d_otimes(s(N1,L1,Av1,Ap1),s(N2,L2,Av2,Ap2),s(N3,L3,Av3,Ap3)) :-
   nl,write('Tentative de conjonction multiplicative a droite (cas 3)'),
   (var(N2) -> /* CAS 2 : A1 et A3 ---> A2 */
      (membre(otimes(L3),Ap3),set_cardinal(L3,Card),Card > 2,
       del(otimes(L3),Ap3,Ap3_sans_otimes),
       membre(otimes(L1),Ap1),
       set_subset(L1,L3),
       del(otimes(L1),Ap1,Ap1_sans_otimes),
       set_difference(Ap3_sans_otimes,Ap1_sans_otimes,Ap2_sans_B),
       set_difference(L3,L1,[B]),
       conc([B],Ap2_sans_B,Ap2),
       set_difference(Av3,Av1,Av2),
       genname(N1,N3,N2),
       nl,write('   Elimination reussie...'),
       nl,write('   A1 : '),write(s(N1,L1,Av1,Ap1)),
       nl,write('   A3 : '),write(s(N3,L3,Av3,Ap3)),
       nl,write('   A2 : '),write(s(N2,L2,Av2,Ap2))
      );       /* CAS 1 : A1 et A2 ---> A3 */
      (\+(membre(otimes(_),Ap2)),membre(otimes(L),Ap1),
       membre(B,Ap2),del(B,Ap2,Ap2_sans_B),
       del(otimes(L),Ap1,Ap1_sans_otimes),
       conc(L,[B],L_otimes_B),
       conc([otimes(L_otimes_B)],Ap2_sans_B,Ap3_sans_Ap1_sans_otimes),
       conc(Ap3_sans_Ap1_sans_otimes,Ap1_sans_otimes,Ap3),
       conc(Av1,Av2,Av3),
       genname(N1,N2,N3)
      )),!.

/* cas 4 : A = otimes(L1) et B = otimes(L2) et A*B = otimes([L1 | L2]) avec  */
/*         Card(L1) >= 2 et Card(L2) >= 2                                    */
d_otimes(s(N1,L1,Av1,Ap1),s(N2,L2,Av2,Ap2),s(N3,L3,Av3,Ap3)) :-
   nl,write('Tentative de conjonction multiplicative a droite (cas 4)'),
   (var(N2) -> /* CAS 2 : A1 et A3 ---> A2 */
      (membre(otimes(L3),Ap3),set_cardinal(L3,Card_L3),Card_L3 > 3,
       del(otimes(L3),Ap3,Ap3_sans_otimes),
       membre(otimes(L1),Ap1),
       set_subset(L1,L3),
       del(otimes(L1),Ap1,Ap1_sans_otimes),
       set_difference(Ap3_sans_otimes,Ap1_sans_otimes,Ap2_sans_otimes),
       set_difference(L3,L1,L2),
       conc([otimes(L2)],Ap2_sans_otimes,Ap2),
       set_difference(Av3,Av1,Av2),
       genname(N1,N3,N2),
       nl,write('   Elimination reussie...'),
       nl,write('   A1 : '),write(s(N1,L1,Av1,Ap1)),
       nl,write('   A3 : '),write(s(N3,L3,Av3,Ap3)),
       nl,write('   A2 : '),write(s(N2,L2,Av2,Ap2))
      );       /* CAS 1 : A1 et A2 ---> A3 */
      (membre(otimes(L2),Ap2),membre(otimes(L1),Ap1),
       del(otimes(L2),Ap2,Ap2_sans_otimes),
       del(otimes(L),Ap1,Ap1_sans_otimes),
       conc(L1,L2,L3),
       conc([otimes(L3)],Ap2_sans_otimes,Ap3_sans_Ap1_sans_otimes),
       conc(Ap3_sans_Ap1_sans_otimes,Ap1_sans_otimes,Ap3),
       conc(Av1,Av2,Av3),
       genname(N1,N2,N3)
      )).

/*===========================================================================*/
/* coupure/3 :                                                               */
/* Elimination d'une formule dans le consequent d'un sequent et qui apparait */
/* dans l'antecedent d'un autre sequent. On forme alors un nouveau sequent   */
/* en supprimant cette formule la ou elle se trouve (i.e. dans le consequent */
/* du premier sequent et dans l'antecedent du second sequent) ; le premier   */
/* sequent est "G |- A,D", le second est "G',A |- D'", la formule supprimee  */
/* est "A" et le nouveau sequent cree est "G,G' |- D,D'") :                  */
/*                                                                           */
/*                   G |- A,D    G',A |- D'                                  */
/*                  ------------------------                                 */
/*                        G,G' |- D,D'                                       */
/*                                                                           */
/* La coupure peut bien sur se faire des deux premiers sequents vers le troi-*/
/* sieme ou bien du troisieme et l'un des deux premiers vers celui qui reste.*/
/* Dans ce cas, par convention, on supposera que l'on construit le deuxieme  */
/* sequent a partir du premier et du troisieme :                             */
/*                                                                           */
/*  CAS 1 :  G |- A,D  et  G',A  |- D'   construisent  G ,G' |- D,D'         */
/*  CAS 2 :  G |- A,D  et  G ,G' |- D,D' construisent  G',A  |- D'           */
/*                                                                           */
/* NOTE : A est une formule. Cela peut donc etre un atome ou bien une        */
/* conjonction multiplicative.                                               */
/*---------------------------------------------------------------------------*/
coupure(s(N1,L1,Av1,Ap1),s(N2,L2,Av2,Ap2),s(N3,L3,Av3,Ap3)) :-
   nl,nl,write('-----> Tentative de coupure '),
   (var(N2) -> /* CAS 2 : A1 et A3 ---> A2 */
      (write('(de A1 et A3 vers A2) :'),
       membre(A,Ap1),
       del(A,Ap1,Ap1_sans_A),
       set_difference(Ap3,Ap1_sans_A,Ap2),
       set_difference(Av3,Av1,Av2_sans_A),
       conc(Av2_sans_A,[A],Av2),
       genname(N1,N3,N2),
       nl,write('   Coupure reussie...'),
       nl,write('   A1 : '),write(s(N1,L1,Av1,Ap1)),
       nl,write('   A3 : '),write(s(N3,L3,Av3,Ap3)),
       nl,write('   A2 : '),write(s(N2,L2,Av2,Ap2))
      );       /* CAS 1 : A1 et A2 ---> A3 */
      (write('(de A1 et A2 vers A3) :'),
       membre(A,Ap1),membre(A,Av2),
       del(A,Ap1,Ap1_sans_A),del(A,Av2,Av2_sans_A),
       conc(Av1,Av2_sans_A,Av3),
       conc(Ap1_sans_A,Ap2,Ap3),
       genname(N1,N2,N3),
       nl,write('   Coupure reussie...'),
       nl,write('   A1 : '),write(s(N1,L1,Av1,Ap1)),
       nl,write('   A2 : '),write(s(N2,L2,Av2,Ap2)),
       nl,write('   A3 : '),write(s(N3,L3,Av3,Ap3))
      )).

/*===========================================================================*/
/* axiome/2                                                                  */
/* Code le sequent identite :   A |- A                                       */
/*---------------------------------------------------------------------------*/
axiome(A,s(identite,[],[A],[A])).

/*****************************************************************************/
/* Clauses pour la planification :                                           */
/*===========================================================================*/
/* Construction du sequent initial a prouver :                               */
/*  - cdsiap/3                                                               */
/*---------------------------------------------------------------------------*/
cdsiap(Ei,Ef,s(but,[],Ei,[otimes(Ef)])) :-
   set_cardinal(Ef,Card),Card > 1.
cdsiap(Ei,Ef,s(but,[],Ei,Ef)).

/*****************************************************************************/
/* Reduction d'un sequent en un sous-sequent plus simple :                   */
/*  - reduire/4                                                              */
/*---------------------------------------------------------------------------*/
reduire(Pin,s(N,L,A,C),s(Nas,Las,Aas,Cas),
        Pout,s(Nout,Lout,Aout,Cout)) :-
   coupure(s(Nas,Las,Aas,Cas),s(N1,L1,A1,C1),s(N,L,A,C)),
   nl,write('Sequent apres coupure : '),write(s(N1,L1,A1,C1)),

   eliminer_otimes(s(N1,L1,A1,C1),s(N2,L2,A2,C2)),
   nl,write('Sequent apres elimination de otimes a gauche : '),
   write(s(N2,L2,A2,C2)),

   eliminer_axiomes(s(N2,L2,A2,C2),s(Nout,Lout,Aout,Cout)),
   nl,write('Sequent apres elimination des axiomes : '),
   write(s(Nout,Lout,Aout,Cout)),
   conc([s(Nas,Las,Aas,Cas)],Pin,Pout).

eliminer_otimes(s(N1,L1,A1,C1),s(N,L,A,C)) :-
   membre(otimes(_),A1),
   g_otimes(s(Nint,Lint,Aint,Cint),s(N1,L1,A1,C1)),
   eliminer_otimes(s(Nint,Lint,Aint,Cint),s(N,L,A,C)).
eliminer_otimes(s(N,L,A,C),s(N,L,A,C)) :-
   \+(membre(otimes(_),A)).

eliminer_axiomes(s(N2,L2,A2,C2),s(N,L,A,C)) :-
   membre(F,A2),
   membre(otimes(Otimes),C2),
   membre(F,Otimes),
   d_otimes(s(identite,[],[F],[F]),s(Nint,Lint,Aint,Cint),s(N2,L2,A2,C2)),
   eliminer_axiomes(s(Nint,Lint,Aint,Cint),s(N,L,A,C)).
eliminer_axiomes(s(N,L,A,C),s(N,L,A,C)).

/*****************************************************************************/
/* Le toplevel du planner...                                                 */
/*  - final/2                          Propose le plan trouve si EN est vide */
/*  - csll/0                           L'acces au planner pour l'utilisateur */
/*****************************************************************************/
final(Preuve_Trouvee) :-
   nl,nl,write('---------------> CSLL vous propose une preuve !'),
   nl,nl,write('-----> Preuve      : '),write(Preuve_Trouvee)/*,
   nl,nl,write('Voulez-vous une autre preuve (oui/non) ?- '),read(Reponse),
   Reponse = non ->
   (nl,write('See you next on TV CSLL !'),nl);
   fail*/.

/* Ce que devra appeller l'utilisateur */
csll(NEI,NEF,NOPS) :-
   /* Recuperation de l'etat initial */
   pb(ei,NEI,etat_initial(Ei)),
   /* Affichage de l'etat initial */
   nl,write('Etat initial : '),write(Ei),nl,
   
   /* Recuperation de l'etat final */
   pb(ef,NEF,etat_final(Ef)),
   /* Affichage de l'etat final */
   nl,write('Etat final a atteindre : '),write(Ef),nl,
   
   /* Creation du sequent initial : setup pour l'algo de preuve... */
   cdsiap(Ei,Ef,Sequent_initial_a_prouver),
   nl,write('Sequent initial a prouver : '),write(Sequent_initial_a_prouver),
   
   /* Lecture de la taille maximal du plan a trouver */
   nl,nl,write('Nombre maximum de action-sequents dans la preuve ? '),read(LP),

   /* Et hop ! On y court, on y court ! */
   assert(used(0)),
   time(profondeur(NOPS,[],Sequent_initial_a_prouver,LP),Duration),
   nl,nl,write('Temps mis pour trouver la premiere preuve : '),
   write(Duration),write(' ms'),
   nl,write('Espace necessaire trouver la premiere preuve : '),
   used(Espace),write(Espace),
   nl,write('See you next on TV CSLL !'),nl,
   retract(used(Espace)).

/*****************************************************************************/
/* La profondeur d'abord comme structure de controle de CSLL :               */
/* (pas efficace, mais facile a programmer !)                                */
/*  - parcourir_en_profondeur/3 Pour continuer ou arreter, selon les valeurs */
/*****************************************************************************/
profondeur(NOPS,P,S,MaxProofLength) :-
   parcourir_en_profondeur(NOPS,P,S,MaxProofLength).

parcourir_en_profondeur(NOPS,Preuve,s(Nap,Lap,Aap,Cap),_) :-
   pb(ops,NOPS,Ops),
   membre(s(N,L,A,C),Ops),
   set_difference(A,Aap,[]),
   (membre(otimes(Otimes),C) ->
      (membre(otimes(Otimesap),Cap),
       set_difference(Otimesap,Otimes,[]),!
      );
      (set_difference(C,Cap,[]),!
      )),
   final([s(N,L,A,C)|Preuve]).

parcourir_en_profondeur(NOPS,Preuve,s(Nap,Lap,Aap,Cap),LPin) :-
   nl,nl,nl,
   write('Nouveau sequent a prouver '),
   write('================================================'),

   nl,nl,write('----> Preuve en cours   : '),write(Preuve),
   nl,nl,write('----> Sequent a prouver : '),write(s(Nap,Lap,Aap,Cap)),

/* Trouver une action compatible avec l'antecedent du sequent a prouver */
   nl,nl,write('Rechercher une action sequent...'),
     pb(ops,NOPS,Ops),
     membre(s(Nas,Las,Aas,Cas),Ops),
     set_included(Aas,Aap),
     nl,nl,write('   ---> Sequent action choisi : '),
     write(s(Nas,Las,Aas,Cas)),
     LPout is LPin - 1,LPout > 0,

/* Trouver une reduction du sequent a prouver */
   nl,nl,write('Reduction du sequent a prouver...'),
     reduire(Preuve,s(Nap,Lap,Aap,Cap),s(Nas,Las,Aas,Cas),Preuve_out,Sout),

   space,

   parcourir_en_profondeur(NOPS,Preuve_out,Sout,LPout).

/*****************************************************************************/
/* MISES EN OEUVRE DES CLAUSES CI-DESSUS                                     */
/* ------------------------------------------------------------------------- */
/* Comprend les exemples ci-dessous :                                        */
/*   - Le monde des cubes (6 exemples)                                       */
/*   - L'echange de deux registres                                           */
/*****************************************************************************/
/* Les operateurs et les exemples 1 et 2 du monde des cubes ; et l'exemple   */
/* des registres est d'apres :                                               */
/* Titre       : Planification et Logique Lineaire                           */
/* Auteurs     : Marcel Masseron, Christophe Tollu, Jacqueline Vauzeilles.   */
/* Publication : Congres RFIA (1991) pages 751 a 761.                        */
/*===========================================================================*/
/* Pour l'exemple 1, il s'agit ici de montrer le sequent :                   */
/*                                                                           */
/*   [mainvide,libre(c),sur(c,a),surtable(b),libre(b)]                       */
/*   |-                                                                      */
/*   [otimes([surtable(c),mainvide,sur(b,a),libre(b),libre(c)])]             */
/*                                                                           */
/* ou "mainvide,libre(c),sur(c,a),surtable(b),libre(b)" sont des axiomes     */
/* d'etat courant, i.e. cela decrit l'etat initial ; et la conjonction multi-*/
/* plicatives "otimes([surtable(c),mainvide,sur(b,a),libre(b),libre(c)])"    */
/* decrit l'etat final a atteindre.                                          */
/*---------------------------------------------------------------------------*/
/* EXEMPLE 1 : L'exemple du papier ci-dessus : */
pb(ei,ex1,etat_initial([surtable(b),sur(c,a),libre(b),libre(c),mainvide])).
pb(ef,ex1,etat_final([surtable(c),mainvide,sur(b,a),libre(b),libre(c)])).

/* EXEMPLE 2 : Un exemple plus simple : */
pb(ei,ex2,etat_initial([surtable(b),sur(c,a),libre(c),libre(b),mainvide])).
pb(ef,ex2,etat_final([mainvide,surtable(c),libre(c)])).

/* EXEMPLE 3 : Un premier pas vers l'anomalie de Sussman : */
pb(ei,ex3,etat_initial([surtable(b),sur(c,a),libre(b),libre(c),mainvide])).
pb(ef,ex3,etat_final([mainvide,libre(b),sur(b,c),surtable(c),libre(a)])).

/* EXEMPLE 4 : Un second pas vers l'anomalie de Sussman : */
/* Note : il faut preciser "surtable(a)", sinon ne trouvera pas de preuve */
pb(ei,ex4,etat_initial([surtable(a),surtable(b),sur(c,a),libre(b),libre(c),mainvide])).
pb(ef,ex4,etat_final([tient(a),libre(b),sur(b,c),surtable(c)])).

/* EXEMPLE 5 : Un troisieme pas vers l'anomalie de Sussman : */
pb(ei,ex5,etat_initial([surtable(a),surtable(b),sur(c,a),libre(b),libre(c),mainvide])).
pb(ef,ex5,etat_final([mainvide,libre(a),sur(a,b),sur(b,c),surtable(c)])).

/* EXEMPLE 6 : Enfin,  l'anomalie de Sussman : */
pb(ei,ex6,etat_initial([surtable(a),surtable(b),sur(c,a),libre(b),libre(c),mainvide])).
pb(ef,ex6,etat_final([mainvide,libre(a),sur(a,b),sur(b,c)])).

/* Les (axiomes de transition) actions :                                     */
pb(ops,ex,[
s(prendre,                                             /* Nom        */
        [X],                                           /* Liaisons   */
        [mainvide,libre(X),surtable(X)],               /* Antecedent */
        [tient(X)]),                                   /* Consequent */

s(oter,                                                /* Nom        */
        [X,Y],                                         /* Liaisons   */
        [mainvide,libre(X),sur(X,Y)],                  /* Antecedent */
        [otimes([tient(X),libre(Y)])]),                /* Consequent */

s(poser,                                               /* Nom        */
        [X],                                           /* Liaisons   */
        [tient(X)],                                    /* Antecedent */
        [otimes([mainvide,libre(X),surtable(X)])]),    /* Consequent */
 
s(mettre,                                              /* Nom        */
        [X,Y],                                         /* Liaisons   */
        [tient(X),libre(Y)],                           /* Antecedent */
        [otimes([mainvide,libre(X),sur(X,Y)])])        /* Consequent */

           ]).

/*---------------------------------------------------------------------------*/
/* Le monde des cubes avec les operateurs classiques                         */
/*---------------------------------------------------------------------------*/
/* L'anomalie de Sussman :                                                   */
pb(ei,as,etat_initial([libre(table),sur(c,a),sur(a,table),
                      sur(b,table),libre(c),libre(b)])).
pb(ef,as,etat_final([libre(a),sur(a,b),
                     libre(table),sur(b,c),sur(c,table)])).

/* Un probleme avec cinq cubes :                                             */
pb(ei,cinqcubes,etat_initial([libre(table),sur(b,a),sur(a,table),libre(b),
                              sur(c,table),sur(d,c),sur(e,d),libre(e)])).
pb(ef,cinqcubes,etat_final([libre(c),sur(c,a),sur(a,table),
                            sur(b,table),sur(d,b),sur(e,d),libre(e)])).

/* Les (axiomes de transition) actions :                                     */
pb(ops,cubes,[

s(newtower,                                              /* Nom        */
   [X,Z],                                                /* Liaisons   */
   [libre(X),sur(X,Z)],                                  /* Antecedent */
   [otimes([libre(X),sur(X,table),libre(Z)])]),          /* Consequent */

s(puton,                                                 /* Nom        */
   [X,Z,Y],                                              /* Liaisons   */
   [libre(X),sur(X,Z),libre(Y)],                         /* Antecedent */
   [otimes([libre(X),sur(X,Y),libre(Z)])])               /* Consequent */

             ]).

/*---------------------------------------------------------------------------*/
/* L'echange de deux registres :                                             */
/*---------------------------------------------------------------------------*/
pb(ei,deuxr,etat_initial([cont(x,a),cont(z,vide),cont(y,b)])).
pb(ef,deuxr,etat_final([cont(z,a),cont(y,a),cont(x,b)])).

/* Les (axiomes de transition) actions :                                     */
pb(ops,deuxr,[
s(assigner,                                       /* Nom        */
         [R,U,S,T],                               /* Liaisons   */
         [cont(R,S),cont(U,T)],                   /* Antecedent */
         [otimes([cont(R,S),cont(U,S)])])         /* Consequent */
             ]).
 
/*---------------------------------------------------------------------------*/
/* Un exemple ne donnant pas un plan non lineaire                            */
/*---------------------------------------------------------------------------*/
pb(ei,expnl,etat_initial([p,u])).
pb(ef,expnl,etat_final([otimes([r,s])])).

pb(ops,expnl,[
s(pq,                      /* Nom        */
   [],                     /* Liaisons   */
   [p],                    /* Antecedent */
   [q]),                   /* Consequent */

s(ut,                      /* Nom        */
   [],                     /* Liaisons   */
   [u],                    /* Antecedent */
   [t]),                   /* Consequent */

s(qr,                      /* Nom        */
   [],                     /* Liaisons   */
   [q],                    /* Antecedent */
   [r]),                   /* Consequent */

s(ts,                      /* Nom        */
   [],                     /* Liaisons   */
   [t],                    /* Antecedent */
   [s])                    /* Consequent */

             ]).
 
/*****************************************************************************/
/* A Linear Bounded Turing Machine (LBA)                                     */
/*                                                                           */
/* Une LBA est une machiede Turing dont la bande de lecture est limite a la  */
/* chaine de symbole qui sont donnes en entree. L'exemple 7.1 (page 150--151)*/
/* de l'ouvrage suivant :                                                    */
/*                                                                           */
/* Auteurs : John Hopcroft et Jeffrey Ullman                                 */
/* Titre   : Introduction to Automata Theory, Languages and Computation      */
/* Editeur : Addison-Wesley (1979)                                           */
/*                                                                           */
/* dont un codage classique, derive de celui de Chapman, est donne plus haut.*/
/* Nous allons maintenant donner un codage beaucoup plus astucieux, derive du*/
/* papier suivant :                                                          */
/*                                                                           */
/* Auteurs : Erol, Nau, Subrahmanian                                         */
/* Tire    : Complexity, Decidability and Undecidability Results for         */
/*           Domain-Independant Planning                                     */
/* Rapport Interne de l'universite du Maryland                               */
/*                                                                           */
/* Dans l'exemple 7.1, il s'agit de verifier que la bande de la machine      */
/* comporte bien autant de 0 que de 1 ; par exemple la bande (| separe deux  */
/* cases de la bande) :                                                      */
/*                                                                           */
/*           ....  B | B | 0 | 0 | 1 | 1 | B | B ....                        */
/*                     c1  c2  c3  c4  c5  c6                                */
/*                                                                           */
/* est une entree correcte, alors que la bande                               */
/*                                                                           */
/*           ....  B | B | 0 | 0 | 0 | 1 | 1 | B | B ....                    */
/*                                                                           */
/* est un entree incorrecte.                                                 */
/* Ceci se fait en remplacant les O par des X et les 1 par des Y, ce qui     */
/* permet de se souvenir qu'on a deja verifie qu'il y avait autant de X que  */
/* de Y.                                                                     */
/*****************************************************************************/
pb(ei,lba,etat_initial([configuration(0,0,1,1,droite,q0,p1)])).
pb(ef,lba,etat_final([configuration(_,_,_,_,_,q4,_)])).
                               
/*****************************************************************************/
/* Les operateurs (au nombre de 41...)                                       */
/*****************************************************************************/
pb(ops,lba,[
/* Le codage de (q0,0) -> (q1,X,R)                                           */
s(q0_0_p1,                                              /* Nom        */
   [V2,V3,V4,V5],                                       /* Liaisons   */
   [configuration(0,V2,V3,V4,V5,q0,p1)],                /* Antecedent */
   [otimes([configuration(0,V2,V3,V4,V5,q0,p1),
            configuration(x,V2,V3,V4,V5,q1,p2)])]),     /* Consequent */

s(q0_0_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,0,V3,V4,V5,q0,p2)],                /* Antecedent */
   [otimes([configuration(V1,0,V3,V4,V5,q0,p2),
            configuration(V1,x,V3,V4,V5,q1,p3)])]),     /* Consequent */

s(q0_0_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,0,V4,V5,q0,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,0,V4,V5,q0,p3),
            configuration(V1,V2,x,V4,V5,q1,p4)])]),     /* Consequent */

s(q0_0_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,0,V5,q0,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,0,V5,q0,p4),
            configuration(V1,V2,V3,x,V5,q1,p5)])]),     /* Consequent */

/* Le codage de (q0,y) -> (q3,y,R)                                           */
s(q0_y_p1,                                              /* Nom        */
  [V2,V3,V4,V5],                                        /* Liaisons   */
   [configuration(y,V2,V3,V4,V5,q0,p1)],                /* Antecedent */
   [otimes([configuration(y,V2,V3,V4,V5,q0,p1),
            configuration(y,V2,V3,V4,V5,q3,p2)])]),     /* Consequent */

s(q0_y_p2,                                              /* Nom        */ 
  [V1,V3,V4,V5],                                        /* Liaisons   */
   [configuration(V1,y,V3,V4,V5,q0,p2)],                /* Antecedent */
   [otimes([configuration(V1,y,V3,V4,V5,q0,p2),
            configuration(V1,y,V3,V4,V5,q3,p3)])]),     /* Consequent */

s(q0_y_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,y,V4,V5,q0,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,y,V4,V5,q0,p3),
            configuration(V1,V2,y,V4,V5,q3,p4)])]),     /* Consequent */

s(q0_y_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,y,V5,q0,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,y,V5,q0,p4),
            configuration(V1,V2,V3,y,V5,q3,p5)])]),     /* Consequent */

/* Le codage de (q1,0) -> (q1,0,R)                                           */
s(q1_0_p1,                                              /* Nom        */
   [V2,V3,V4,V5],                                       /* Liaisons   */
   [configuration(0,V2,V3,V4,V5,q1,p1)],                /* Antecedent */
   [otimes([configuration(0,V2,V3,V4,V5,q1,p1),
            configuration(0,V2,V3,V4,V5,q1,p2)])]),     /* Consequent */
                                                       
s(q1_0_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,0,V3,V4,V5,q1,p2)],                /* Antecedent */
   [otimes([configuration(V1,0,V3,V4,V5,q1,p2),
            configuration(V1,0,V3,V4,V5,q1,p3)])]),     /* Consequent */

s(q1_0_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,0,V4,V5,q1,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,0,V4,V5,q1,p3),
            configuration(V1,V2,0,V4,V5,q1,p4)])]),     /* Consequent */

s(q1_0_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,0,V5,q1,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,0,V5,q1,p3),
            configuration(V1,V2,V3,0,V5,q1,p4)])]),     /* Consequent */

/* Le codage de (q1,1) -> (q2,y,L)                                           */
s(q1_1_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,1,V3,V4,V5,q1,p2)],                /* Antecedent */
   [otimes([configuration(V1,1,V3,V4,V5,q1,p2),
            configuration(V1,y,V3,V4,V5,q2,p1)])]),     /* Consequent */

s(q1_1_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,1,V4,V5,q1,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,1,V4,V5,q1,p3),
            configuration(V1,V2,y,V4,V5,q2,p2)])]),     /* Consequent */

s(q1_1_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,1,V5,q1,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,1,V5,q1,p4),
            configuration(V1,V2,V3,y,V5,q2,p3)])]),     /* Consequent */

s(q1_1_p5,                                              /* Nom        */
   [V1,V2,V3,V4],                                       /* Liaisons   */
   [configuration(V1,V2,V3,V4,1,q1,p5)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,V4,1,q1,p5),
            configuration(V1,V2,V3,V4,y,q2,p4)])]),     /* Consequent */

/* Le codage de (q1,y) -> (q1,y,R)                                           */
s(q1_y_p1,                                              /* Nom        */
   [V2,V3,V4,V5],                                       /* Liaisons   */
   [configuration(y,V2,V3,V4,V5,q1,p1)],                /* Antecedent */
   [otimes([configuration(y,V2,V3,V4,V5,q1,p1),
            configuration(y,V2,V3,V4,V5,q1,p2)])]),     /* Consequent */

s(q1_y_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,y,V3,V4,V5,q1,p2)],                /* Antecedent */
   [otimes([configuration(V1,y,V3,V4,V5,q1,p2),
            configuration(V1,y,V3,V4,V5,q1,p3)])]),     /* Consequent */

s(q1_y_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,y,V4,V5,q1,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,y,V4,V5,q1,p3),
            configuration(V1,V2,y,V4,V5,q1,p4)])]),     /* Consequent */

s(q1_y_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,y,V5,q1,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,y,V5,q1,p4),
            configuration(V1,V2,V3,y,V5,q1,p5)])]),     /* Consequent */

/* Le codage de (q2,0) -> (q2,0,L)                                           */
s(q2_0_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,0,V3,V4,V5,q2,p2)],                /* Antecedent */
   [otimes([configuration(V1,0,V3,V4,V5,q2,p2),
            configuration(V1,0,V3,V4,V5,q2,p1)])]),     /* Consequent */

s(q2_0_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,0,V4,V5,q2,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,0,V4,V5,q2,p3),
            configuration(V1,V2,0,V4,V5,q2,p2)])]),     /* Consequent */
                                                       
s(q2_0_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,0,V5,q2,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,0,V5,q2,p4),
            configuration(V1,V2,V2,0,V5,q2,p3)])]),     /* Consequent */

s(q2_0_p5,                                              /* Nom        */
   [V1,V2,V3,V4],                                       /* Liaisons   */
   [configuration(V1,V2,V3,V4,0,q2,p5)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,V4,0,q2,p5),
            configuration(V1,V2,V2,V4,0,q2,p4)])]),     /* Consequent */

/* Le codage de (q2,x) -> (q0,x,R)                                           */
s(q2_x_p1,                                              /* Nom        */ 
   [V2,V3,V4,V5],                                       /* Liaisons   */
   [configuration(x,V2,V3,V4,V5,q2,p1)],                /* Antecedent */
   [otimes([configuration(x,V2,V3,V4,V5,q2,p1),
              configuration(x,V2,V3,V4,V5,q0,p2)])]),   /* Consequent */

s(q2_x_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,x,V3,V4,V5,q2,p2)],                /* Antecedent */
   [otimes([configuration(V1,x,V3,V4,V5,q2,p2),
            configuration(V1,x,V3,V4,V5,q0,p3)])]),     /* Consequent */

s(q2_x_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,x,V4,V5,q2,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,x,V4,V5,q2,p3),
            configuration(V1,V2,x,V4,V5,q0,p4)])]),     /* Consequent */

s(q2_x_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,x,V5,q2,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,x,V5,q2,p4),
            configuration(V1,V2,V3,x,V5,q0,p5)])]),     /* Consequent */

/* Le codage de (q2,y) -> (q2,y,L)                                           */
s(q2_y_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,y,V3,V4,V5,q2,p2)],                /* Antecedent */
   [otimes([configuration(V1,y,V3,V4,V5,q2,p2),
            configuration(V1,y,V3,V4,V5,q2,p1)])]),     /* Consequent */

s(q2_y_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,y,V4,V5,q2,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,y,V4,V5,q2,p3),
            configuration(V1,V2,y,V4,V5,q2,p2)])]),     /* Consequent */

s(q2_y_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,y,V5,q2,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,y,V5,q2,p4),
            configuration(V1,V2,V3,y,V5,q2,p3)])]),     /* Consequent */

s(q2_y_p5,                                              /* Nom        */
   [V1,V2,V3,V4],                                       /* Liaisons   */
   [configuration(V1,V2,V3,V4,y,q2,p5)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,V4,y,q2,p5),
            configuration(V1,V2,V3,V4,y,q2,p4)])]),     /* Consequent */

/* Le codage de (q3,y) -> (q3,y,R)                                           */
s(q3_y_p1,                                              /* Nom        */
   [V2,V3,V4,V5],                                       /* Liaisons   */
   [configuration(y,V2,V3,V4,V5,q3,p1)],                /* Antecedent */
   [otimes([configuration(y,V2,V3,V4,V5,q3,p1),
            configuration(y,V2,V3,V4,V5,q3,p2)])]),     /* Consequent */

s(q3_y_p2,                                              /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,y,V3,V4,V5,q3,p2)],                /* Antecedent */
   [otimes([configuration(V1,y,V3,V4,V5,q3,p2),
            configuration(V1,y,V3,V4,V5,q3,p3)])]),     /* Consequent */

s(q3_y_p3,                                              /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,y,V4,V5,q3,p3)],                /* Antecedent */
   [otimes([configuration(V1,V2,y,V4,V5,q3,p3),
            configuration(V1,V2,y,V4,V5,q3,p4)])]),     /* Consequent */

s(q3_y_p4,                                              /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,y,V5,q3,p4)],                /* Antecedent */
   [otimes([configuration(V1,V2,V3,y,V5,q3,p4),
            configuration(V1,V2,V3,y,V5,q3,p5)])]),     /* Consequent */

/* Le codage de (q3,droite) -> (q4,droite,R)                                 */
s(q3_droite_p1,                                         /* Nom        */
   [V2,V3,V4,V5],                                       /* Liaisons   */
   [configuration(droite,V2,V3,V4,V5,q3,p1)],           /* Antecedent */
   [otimes([configuration(droite,V2,V3,V4,V5,q3,p1),
            configuration(droite,V2,V3,V4,V5,q4,p2)])]),/* Consequent */ 

s(q3_droite_p2,                                         /* Nom        */
   [V1,V3,V4,V5],                                       /* Liaisons   */
   [configuration(V1,droite,V3,V4,V5,q3,p2)],           /* Antecedent */
   [otimes([configuration(V1,droite,V3,V4,V5,q3,p2),
            configuration(V1,droite,V3,V4,V5,q4,p3)])]),/* Consequent */

s(q3_droite_p3,                                         /* Nom        */
   [V1,V2,V4,V5],                                       /* Liaisons   */
   [configuration(V1,V2,droite,V4,V5,q3,p3)],           /* Antecedent */
   [otimes([configuration(V1,V2,droite,V4,V5,q3,p3),
            configuration(V1,V2,droite,V4,V5,q4,p4)])]),/* Consequent */

s(q3_droite_p4,                                         /* Nom        */
   [V1,V2,V3,V5],                                       /* Liaisons   */
   [configuration(V1,V2,V3,droite,V5,q3,p4)],           /* Antecedent */
   [otimes([configuration(V1,V2,V3,droite,V5,q3,p4),    
            configuration(V1,V2,V3,droite,V5,q4,p5)])]),/* Consequent */
    
s(q3_droite_p5,                                         /* Nom        */
   [V1,V2,V3,V4],                                       /* Liaisons   */
   [configuration(V1,V2,V3,V4,droite,q3,p5)],           /* Antecedent */
   [otimes([configuration(V1,V2,V3,V4,droite,q3,p5),
            configuration(V1,V2,V3,V4,droite,q4,p5)])]) /* Consequent */

                ]).

/*****************************************************************************/
/* Un exemple de l'utilisation de la conjonction multiplicative pour compter */
/*****************************************************************************/
pb(ei,m2c,etat_initial([libre(c),sur(b,a),sur(c,b),sur(a,table)])).
pb(ef,m2c,etat_final([q3])).

/* Les operateurs -----------------------------------------------------------*/
pb(ops,m2c,[
s(debut,                                            /* Noms       */
  [X,Y],                                            /* Liaisons   */
  [libre(X),sur(X,Y)],                              /* Antecedent */
  [otimes([q1,libre(Y),cube])]),                    /* Consequent */

s(q1q1,                                             /* Noms       */
  [X,Y],                                            /* Liaisons   */
  [q1,libre(X),sur(X,Y)],                           /* Antecedent */
  [otimes([q1,libre(Y),cube])]),                    /* Consequent */

s(q1q2,                                             /* Noms       */
  [X],                                              /* Liaisons   */
  [q1,sur(X,table)],                                /* Antecedent */
  [otimes([q2,cube])]),                             /* Consequent */

s(q2q3,                                             /* Noms       */
  [],                                               /* Liaisons   */
  [q2],                                             /* Antecedent */
  [q3])                                             /* Consequent */
       ]).

/*****************************************************************************/
/* Fin du fichier csll                                                       */
/*****************************************************************************/
