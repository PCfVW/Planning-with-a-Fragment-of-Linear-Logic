/*****************************************************************************/
/* Forward Chaining Planning                                                 */
/*                                                           [Eric JACOPIN]  */
/*---------------------------------------------------------------------------*/
/* Date de creation      : 04 Novembre 1992                                  */
/* Derniere modification : 06 Novembre 1992                                  */
/*****************************************************************************/

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
   retract(used(N)),   assert(used(M)).

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
/* La construction du plan initial :                                         */
/*  - cpi/2                                     Construction du plan initial */
/*****************************************************************************/
cpi(Plan_in,Plan_out) :-
   etat_initial(Ei),
   etat_final(Ef),
   conc([op(oi,[],[],Ei,[]),op(of,[],Ef,[],[])],Plan_in,Plan_out).

/*****************************************************************************/
/* Le toplevel du planner...                                                 */
/*  - final/2                          Propose le plan trouve si EN est vide */
/*  - fcp/0                           L'acces au planner pour l'utilisateur */
/*****************************************************************************/
final(Plan_Trouve) :-
   nl,nl,nl,
   nl,write('----------> FCP vous propose un plan !'),
   nl,nl,write('-----> Plan      : '),write(Plan_Trouve)/*,
   nl,nl,write('Voulez-vous un autre plan (oui/non) ?- '),read(Reponse),
   Reponse = non ->
   (nl,write('See you next on TV FCP !'),nl);
   fail*/.

/* Ce que devra appeller l'utilisateur */
fcp :-
   /* Affichage des donnees du probleme */
   etat_initial(Ei),nl,write('Etat initial : '),write(Ei),nl,
   etat_final(Ef),nl,write('Etat final a atteindre : '),write(Ef),nl,
   
   /* Creation du plan initial : setup pour l'algo de planif... */
   cpi([],Plan_initial),
   
   /* Lecture de la taille maximal du plan a trouver */
   nl,nl,write('Nombre maximum de action-sequents dans la preuve ? '),read(LP),

   /* Et hop ! On y court, on y court ! */
   assert(used(0)),
   time(profondeur(Plan_initial,Ei,LP,1),
        Duration),
   nl,nl,write('Temps mis pour trouver la premiere preuve : '),
   write(Duration),write(' ms'),
   nl,write('Espace necessaire trouver la premiere preuve : '),
   used(Espace),write(Espace),
   nl,write('See you next on TV FCP !'),nl,
   retract(used(Espace)).

/*****************************************************************************/
/* La profondeur d'abord comme structure de controle de CSLL :               */
/* (pas efficace, mais facile a programmer !)                                */
/*  - parcourir_en_profondeur/4 Pour continuer ou arreter, selon les valeurs */
/*****************************************************************************/
profondeur(Plan,Situation,Taille_maximum_du_plan,C) :-
   parcourir_en_profondeur(Plan,Situation,Taille_maximum_du_plan,C).

parcourir_en_profondeur(The_Plan,The_Situation,_,_) :-
   membre(op(of,_,Ef,_,_),The_Plan),
   set_subset(Ef,The_Situation),
   final(The_Plan).

parcourir_en_profondeur(Pin,Csin,LPin,Cin) :-
    nl,nl,nl,write('Rechercher une description applicable '),
    nl,write('********************************************************'),

    nl,nl,write('----> Plan   : '),write(Pin),

/* a. Trouver un etablisseur */
    op(N,L,P,A,D),
    set_included(P,Csin),
    nl,nl,write('   ---> Description applicable : '),
    write(op(N,L,P,A,D)),
    LPout is LPin - 1,LPout > 0,
    Cout is Cin + 1,

   conc(Csin,A,Csint),
   set_difference(Csint,D,Csout),
   nl,nl,write('   ---> Nouvelle situation : '),write(Csout),
   gensym(Nout,N,Cin),
   conc(Pin,[op(Nout,L,P,A,D)],Pout),

   space,

   parcourir_en_profondeur(Pout,Csout,LPout,Cout).

/*****************************************************************************/
/*          MISE    EN    OEUVRE    DES    CLAUSES    CI-DESSUS              */
/*****************************************************************************/
/* Cubes et main de robot                                                    */
/* Exemple d'apres :                                                         */
/* Titre       : Planification et Logique Lineaire                           */
/* Auteurs     : Marcel Masseron, Christophe Tollu, Jacqueline Vauzeilles.   */
/* Publication : Congres RFIA (1991) pages 751 a 761.                        */
/* Les memes exemples sont codes pour le planificateur en logique lineaire   */
/*===========================================================================*/
/* L'etat initial et l'etat final                                            */
/*---------------------------------------------------------------------------*/
/* EXEMPLE 1 : L'exemple du papier ci-dessus : */
/*etat_initial([surtable(b),sur(c,a),libre(b),libre(c),mainvide]).
/*etat_final([surtable(c),mainvide,sur(b,a),libre(b),libre(c)]).

/* EXEMPLE 2 : Un exemple plus simple : */
/*etat_initial([surtable(b),sur(c,a),libre(c),libre(b),mainvide]).
/*etat_final([mainvide,surtable(c),libre(c)]).

/* EXEMPLE 3 : Un premier pas vers l'anomalie de Sussman : */
/*etat_initial([surtable(b),sur(c,a),libre(b),libre(c),mainvide]).
/*etat_final([mainvide,libre(b),sur(b,c),surtable(c),libre(a)]).

/* EXEMPLE 4 : Un second pas vers l'anomalie de Sussman : */
/* Note : il faut preciser "surtable(a)", sinon ne trouvera pas de preuve */
/*etat_initial([surtable(a),surtable(b),sur(c,a),libre(b),libre(c),mainvide]).
/*etat_final([tient(a),libre(b),sur(b,c),surtable(c)]).

/* EXEMPLE 5 : Un troisieme pas vers l'anomalie de Sussman : */
etat_initial([surtable(a),surtable(b),sur(c,a),libre(b),libre(c),mainvide]).
etat_final([mainvide,libre(a),sur(a,b),sur(b,c),surtable(c)]).

/* EXEMPLE 6 : Enfin,  l'anomalie de Sussman : */
/*etat_initial([surtable(a),surtable(b),sur(c,a),libre(b),libre(c),mainvide]).
/*etat_final([mainvide,libre(a),sur(a,b),sur(b,c)]).

/*****************************************************************************/
/* Les operateurs                                                            */
/*****************************************************************************/
op(prendre,                                       /* Nom           */
   [X],                                           /* Liaisons      */
   [mainvide,libre(X),surtable(X)],               /* Preconditions */
   [tient(X)],                                    /* Add-List      */
   [mainvide,libre(X),surtable(X)]).              /* Delete-List   */

op(oter,                                          /* Nom           */
   [X,Y],                                         /* Liaisons      */
   [mainvide,libre(X),sur(X,Y)],                  /* Preconditions */
   [tient(X),libre(Y)],                           /* Add-List      */
   [mainvide,libre(X),sur(X,Y)]).                 /* Delete-List   */

op(poser,                                         /* Nom           */
   [X],                                           /* Liaisons      */
   [tient(X)],                                    /* Preconditions */
   [mainvide,libre(X),surtable(X)],               /* Add-List      */
   [tient(X)]).                                   /* Delete-List   */

op(mettre,                                        /* Nom           */
   [X,Y],                                         /* Liaisons      */
   [tient(X),libre(Y)],                           /* Preconditions */
   [mainvide,libre(X),sur(X,Y)],                  /* Add-List      */
   [tient(X),libre(Y)]).                          /* Delete-List   */

/*****************************************************************************/
/*             ECHANGE      DE      DEUX      REGISTRES                      */
/*---------------------------------------------------------------------------*/
/* L'etat initial et l'etat final                                            */
/*****************************************************************************/
/*etat_initial([cont(x,a),cont(z,vide),cont(y,b)]).
/*etat_final([cont(z,a),cont(y,a),cont(x,b)]).

/* L'operateur : *************************************************************/
/*op(assigner,                                        /* Nom           */
/*   [R,U,S,T],                                       /* Liaisons      */
/*   [cont(R,S),cont(U,T)],                           /* Preconditions */
/*   [cont(U,S)],                                     /* Add-List      */
/*   [cont(U,T)]).                                    /* Delete-List   */
 
/*****************************************************************************/
/* L'etat initial et l'etat final du probleme de Sussman                     */
/*****************************************************************************/
etat_initial([libre(table),sur(c,a),sur(a,table),
              sur(b,table),libre(c),libre(b)]).
etat_final([sur(a,b),sur(b,c)]).
etat_final([libre(a),sur(a,b),libre(table),
            sur(b,c),sur(c,table)]).

/*****************************************************************************/
/* Un probleme avec 5 cubes...                                               */
/*****************************************************************************/
/* L'etat initial et l'etat final du probleme avec 5 cubes.                  */
/*****************************************************************************/
/*etat_initial([libre(table),sur(b,a),sur(a,table),libre(b),
/*              sur(c,table),sur(d,c),sur(e,d),libre(e)]).  
/*etat_final([libre(c),sur(c,a),sur(d,b),sur(e,d),libre(e)]).

/*****************************************************************************/
/* Les operateurs. La structure de donnees choisies pour representer un ope- */
/* rateur est basee sur celle de McCluskey : Un operateur est un quintuplet  */
/* (Nom,Liaisons,Preconditions,Add-list,Delete-list) dont tous les elements  */
/* sauf le premier (le nom de l'operateur) sont des listes PROLOG.           */
/*****************************************************************************/
/* Les'operateurs : Newtower et Puton                                        */
op(newtower,                      /* Nom           */
   [X,Z],                         /* Liaisons      */
   [sur(X,Z),libre(X)],           /* Preconditions */
   [sur(X,table),libre(Z)],       /* Add-list      */
   [sur(X,Z)]).                   /* Delete-list   */

op(puton,                         /* Nom           */
   [X,Y,Z],                       /* Liaisons      */
   [sur(X,Z),libre(X),libre(Y)],  /* Preconditions */
   [sur(X,Y),libre(Z)],           /* Add-list      */
   [sur(X,Z),libre(Y)]).          /* Delete-list   */

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
/*
/* dont un codage classique, derive de celui de Chapman, est donne plus haut.*/
/* Nous allons maintenant donner un codage beaucoup plus astucieux, derive du*/
/* papier suivant :
/*                                                                          */
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
/* etat_initial([configuration(0,0,1,1,droite,q0,p1)]).
/* etat_final([configuration(_,_,_,_,_,q4,_)]).
                               
/*****************************************************************************/
/* Les operateurs (au nombre de 41...)                                       */
/*****************************************************************************/
/* Le codage de (q0,0) -> (q1,X,R)                                           */
/*op(q0_0_p1,                                            /* Nom           */
/*   [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(0,V2,V3,V4,V5,q0,p1)],               /* Preconditions */
/*   [configuration(x,V2,V3,V4,V5,q1,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */

/*op(q0_0_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,0,V3,V4,V5,q0,p2)],               /* Preconditions */
/*   [configuration(V1,x,V3,V4,V5,q1,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q0_0_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,0,V4,V5,q0,p3)],               /* Preconditions */
/*   [configuration(V1,V2,x,V4,V5,q1,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q0_0_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,0,V5,q0,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,x,V5,q1,p5)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q0,y) -> (q3,y,R)                                           */
/*op(q0_y_p1,                                            /* Nom           */
/*  [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(y,V2,V3,V4,V5,q0,p1)],               /* Preconditions */
/*   [configuration(y,V2,V3,V4,V5,q3,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q0_y_p2,                                            /* Nom           */ 
/*  [V1,V3,V4,V5],                                       /* Liaisons      */
/*   [configuration(V1,y,V3,V4,V5,q0,p2)],               /* Preconditions */
/*   [configuration(V1,y,V3,V4,V5,q3,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q0_y_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,y,V4,V5,q0,p3)],               /* Preconditions */
/*   [configuration(V1,V2,y,V4,V5,q3,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q0_y_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,y,V5,q0,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,y,V5,q3,p5)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q1,0) -> (q1,0,R)                                           */
/*op(q1_0_p1,                                            /* Nom           */
/*   [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(0,V2,V3,V4,V5,q1,p1)],               /* Preconditions */
/*   [configuration(0,V2,V3,V4,V5,q1,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_0_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,0,V3,V4,V5,q1,p2)],               /* Preconditions */
/*   [configuration(V1,0,V3,V4,V5,q1,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_0_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,0,V4,V5,q1,p3)],               /* Preconditions */
/*   [configuration(V1,V2,0,V4,V5,q1,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_0_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,0,V5,q1,p3)],               /* Preconditions */
/*   [configuration(V1,V2,V3,0,V5,q1,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q1,1) -> (q2,y,L)                                           */
/*op(q1_1_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,1,V3,V4,V5,q1,p2)],               /* Preconditions */
/*   [configuration(V1,y,V3,V4,V5,q2,p1)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_1_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,1,V4,V5,q1,p3)],               /* Preconditions */
/*   [configuration(V1,V2,y,V4,V5,q2,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_1_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,1,V5,q1,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,y,V5,q2,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_1_p5,                                            /* Nom           */
/*   [V1,V2,V3,V4],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,V4,1,q1,p5)],               /* Preconditions */
/*   [configuration(V1,V2,V3,V4,y,q2,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q1,y) -> (q1,y,R)                                           */
/*op(q1_y_p1,                                            /* Nom           */
/*   [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(y,V2,V3,V4,V5,q1,p1)],               /* Preconditions */
/*   [configuration(y,V2,V3,V4,V5,q1,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_y_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,y,V3,V4,V5,q1,p2)],               /* Preconditions */
/*   [configuration(V1,y,V3,V4,V5,q1,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_y_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,y,V4,V5,q1,p3)],               /* Preconditions */
/*   [configuration(V1,V2,y,V4,V5,q1,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q1_y_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,y,V5,q1,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,y,V5,q1,p5)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q2,0) -> (q2,0,L)                                           */
/*op(q2_0_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,0,V3,V4,V5,q2,p2)],               /* Preconditions */
/*   [configuration(V1,0,V3,V4,V5,q2,p1)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_0_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,0,V4,V5,q2,p3)],               /* Preconditions */
/*   [configuration(V1,V2,0,V4,V5,q2,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_0_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,0,V5,q2,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V2,0,V5,q2,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_0_p5,                                            /* Nom           */
/*   [V1,V2,V3,V4],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,V4,0,q2,p5)],               /* Preconditions */
/*   [configuration(V1,V2,V2,V4,0,q2,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q2,x) -> (q0,x,R)                                           */
/*op(q2_x_p1,                                            /* Nom           */
/*   [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(x,V2,V3,V4,V5,q2,p1)],               /* Preconditions */
/*   [configuration(x,V2,V3,V4,V5,q0,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_x_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,x,V3,V4,V5,q2,p2)],               /* Preconditions */
/*   [configuration(V1,x,V3,V4,V5,q0,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_x_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,x,V4,V5,q2,p3)],               /* Preconditions */
/*   [configuration(V1,V2,x,V4,V5,q0,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_x_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,x,V5,q2,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,x,V5,q0,p5)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q2,y) -> (q2,y,L)                                           */
/*op(q2_y_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,y,V3,V4,V5,q2,p2)],               /* Preconditions */
/*   [configuration(V1,y,V3,V4,V5,q2,p1)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_y_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,y,V4,V5,q2,p3)],               /* Preconditions */
/*   [configuration(V1,V2,y,V4,V5,q2,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_y_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,y,V5,q2,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,y,V5,q2,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q2_y_p5,                                            /* Nom           */
/*   [V1,V2,V3,V4],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,V4,y,q2,p5)],               /* Preconditions */
/*   [configuration(V1,V2,V3,V4,y,q2,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q3,y) -> (q3,y,R)                                           */
/*op(q3_y_p1,                                            /* Nom           */
/*   [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(y,V2,V3,V4,V5,q3,p1)],               /* Preconditions */
/*   [configuration(y,V2,V3,V4,V5,q3,p2)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_y_p2,                                            /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,y,V3,V4,V5,q3,p2)],               /* Preconditions */
/*   [configuration(V1,y,V3,V4,V5,q3,p3)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_y_p3,                                            /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,y,V4,V5,q3,p3)],               /* Preconditions */
/*   [configuration(V1,V2,y,V4,V5,q3,p4)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_y_p4,                                            /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,y,V5,q3,p4)],               /* Preconditions */
/*   [configuration(V1,V2,V3,y,V5,q3,p5)],               /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/* Le codage de (q3,droite) -> (q4,droite,R)                                 */
/*op(q3_droite_p1,                                       /* Nom           */
/*   [V2,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(droite,V2,V3,V4,V5,q3,p1)],          /* Preconditions */
/*   [configuration(droite,V2,V3,V4,V5,q4,p2)],          /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_droite_p2,                                       /* Nom           */
/*   [V1,V3,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,droite,V3,V4,V5,q3,p2)],          /* Preconditions */
/*   [configuration(V1,droite,V3,V4,V5,q4,p3)],          /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_droite_p3,                                       /* Nom           */
/*   [V1,V2,V4,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,droite,V4,V5,q3,p3)],          /* Preconditions */
/*   [configuration(V1,V2,droite,V4,V5,q4,p4)],          /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_droite_p4,                                       /* Nom           */
/*   [V1,V2,V3,V5],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,droite,V5,q3,p4)],          /* Preconditions */
/*   [configuration(V1,V2,V3,droite,V5,q4,p5)],          /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*op(q3_droite_p5,                                       /* Nom           */
/*   [V1,V2,V3,V4],                                      /* Liaisons      */
/*   [configuration(V1,V2,V3,V4,droite,q3,p5)],          /* Preconditions */
/*   [configuration(V1,V2,V3,V4,droite,q4,p5)],          /* Add-list      */
/*   []).                                                /* Delete-list   */
/*
/*****************************************************************************/
/* End of file fcp                                                           */
/*****************************************************************************/

