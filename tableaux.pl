%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Definizione degli operatori logici
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- op(650, xfy, sse).
:- op(640, xfy, implies).
:- op(630, yfx, or).
:- op(620, yfx, and).
:- op(610, fy, not).

% Per i quantificatori usiamo forall(x,fbf) e exists(x,fbf).
% Le costanti devono essere dei numeri, e le lettere in minuscolo sono le variabili


:- op(600, xfy, \).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Predicato per verificare il tipo
%  delle formule ben formate
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_alpha(_ and _).
is_alpha(_ sse _).
is_alpha(not (_ or _)).
is_alpha(not (_ implies _)).

is_beta(_ or _).
is_beta(_ implies _).
is_beta(not (_ and _)).
is_beta(not (_ sse _)).

is_delta(exists( _ , _ )).
is_delta(not forall( _ , _ )).

is_fresh_gamma(forall( X , Y ), forall( X , Y , 0)).
is_fresh_gamma(not exists( X , Y ), not exists( X , Y , 0)).

is_gamma(forall( _ , _ , _ )).
is_gamma(not exists( _ , _ , _ )).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Controllo formula atomica ground
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

atomo_ground(X) :- compound( X ), X =.. [_|Terms], lista_interi(Terms).

lista_interi([]).
lista_interi([Termine | Terms]) :- integer(Termine), lista_interi(Terms).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Controllo formula atomica
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

atomo(X) :- compound( X ), X =.. Parametri, parametri_validi(Parametri).

parametri_validi([]).
parametri_validi([Parametro | Tail]) :- atomic(Parametro),
                    Parametro \== not,
                    Parametro \== and,
                    Parametro \== or,
                    Parametro \== implies,
                    Parametro \== sse,
                    Parametro \== forall,
                    Parametro \== exists,
                    !,
                    parametri_validi(Tail).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Controllo formula ben formata
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fbf_chiusa( X and Y ) :- !, fbf_chiusa(X),fbf_chiusa(Y).
fbf_chiusa( X or Y ) :- !, fbf_chiusa(X), fbf_chiusa(Y).
fbf_chiusa( X implies Y ) :- !, fbf_chiusa(X), fbf_chiusa(Y).
fbf_chiusa( X sse Y ) :- !, fbf_chiusa(X), fbf_chiusa(Y).
fbf_chiusa( forall(X,Y) ) :- atomic(X),instantiate(Y,X,-1,Y1),!, fbf_chiusa(Y1).
fbf_chiusa( exists(X,Y) ) :- atomic(X), instantiate(Y,X,-1,Y1),!,fbf_chiusa(Y1).
fbf_chiusa( not X ) :- ! ,fbf_chiusa(X).
fbf_chiusa( X ) :- atomo_ground(X). 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Instanziazione di fbf quantificate
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

instantiate( X and Y , Var , Par , X1 and Y1) :- !,
                         instantiate(X,Var,Par,X1),
                         instantiate(Y,Var,Par,Y1).
                         
instantiate( X or Y , Var , Par , X1 or Y1) :- !,
                         instantiate(X,Var,Par,X1),
                         instantiate(Y,Var,Par,Y1).
                         
instantiate( X implies Y , Var , Par , X1 implies Y1) :- !,
                             instantiate(X,Var,Par,X1),
                             instantiate(Y,Var,Par,Y1).
                             
instantiate( X sse Y , Var , Par , X1 sse Y1) :- !,
                         instantiate(X,Var,Par,X1),
                         instantiate(Y,Var,Par,Y1).
                             
instantiate( forall(X,Y),Var,Par,forall(X,Y1)) :- X \== Var,
                          !,
                          instantiate(Y,Var,Par,Y1).
                  
%le occorrenze interne della variabile sono bounded nel quantificatore
instantiate( forall(X,Y),Var,_,forall(X,Y)) :- X == Var, !. 

instantiate( exists(X,Y),Var,Par,exists(X,Y1)) :- X \== Var,
                          !,
                          instantiate(Y,Var,Par,Y1).
                          
%le occorrenze interne della variabile sono bounded nel quantificatore
instantiate( exists(X,Y),Var,_,exists(X,Y)) :- X == Var,!.
 
instantiate( not X,Var,Par, not X1 ) :-!, instantiate(X,Var,Par,X1).

instantiate( X,Var,Par,X1 ) :- atomo(X), !, substitute_occurrences(X,Var,Par,X1).


substitute_occurrences(X,Var,Par,X1):- X =.. [Pred|Terms], substitute(Terms,Var,Par,Terms1),X1=.. [Pred|Terms1].


substitute([],_,_,[]).

substitute([Term | Tail],Var,Par,[Term1 | Tail1]) :- Term == Var,Term1 = Par,!, substitute(Tail,Var,Par,Tail1).
substitute([Term | Tail],Var,Par,[Term1 | Tail1]) :- Term \== Var,Term1 = Term,!, substitute(Tail,Var,Par,Tail1).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Algoritmo per il calcolo del Tableau
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prova(Fbf) :- tclose(Fbf, 10). % il numero 10 e' un valore indicativo

tclose(Fbf, Limite) :- fbf_chiusa(Fbf), closed_branch([Fbf],[],[],[],[],[], Limite, 0, []).

closed_branch([Fbf|_],As,Ds,Bs,Gs,Ls,_,_,Elaborate) :- chiude(Fbf,As,Ds,Bs,Gs,Ls),
                             !,
                             stampa_ramo([Fbf],As,Ds,Bs,Gs,Ls,Elaborate,'CHIUSO').
                             
closed_branch([Fbf|Fbfs],As,Ds,Bs,Gs,Ls,Limite,Params,Elaborate):- 
                                \+ chiude(Fbf,As,Ds,Bs,Gs,Ls),
                              push_formula(Fbf,As,Ds,Bs,Gs,Ls,As1,Ds1,Bs1,Gs1,Ls1),
                              !,
                              closed_branch(Fbfs,As1,Ds1,Bs1,Gs1,Ls1,Limite,Params,Elaborate).


closed_branch([],[],[],[],[],Ls,_,_,Elaborate) :- !, stampa_ramo([],[],[],[],[],Ls,Elaborate,'APERTO').

closed_branch([],As,Ds,Bs,Gs,Ls,Limite,Params,Elaborate) :- Params < Limite,
                              !,
                              closed_branch(As,Ds,Bs,Gs,Ls,Limite,Params,Elaborate).
                              
closed_branch([],As,Ds,Bs,Gs,Ls,Limite,Params,Elaborate) :- Params >= Limite,
                              !,
                              stampa_ramo([],As,Ds,Bs,Gs,Ls,Elaborate,'APERTO').


%alpha
closed_branch([Formula|As],Ds,Bs,Gs,Ls,Limite,Params,Elaborate) :- 
                 regola_alpha(Formula,Alpha1,Alpha2),
                 !,
                 closed_branch([Alpha1,Alpha2],As,Ds,Bs,Gs,Ls,Limite,Params,[Formula|Elaborate]).
      
%delta
closed_branch([],[Formula|Ds],Bs,Gs,Ls,Limite,Params,Elaborate) :- 
                 Params < Limite,
                 regola_delta(Formula,Delta1,Limite,Params),
                 Params1 is Params + 1,
                 !,
                 closed_branch([Delta1],[],Ds,Bs,Gs,Ls, Limite,Params1,[Formula|Elaborate]).
%beta                 
closed_branch([],[],[Formula|Bs],Gs,Ls,Limite,Params,Elaborate) :- 
                 regola_beta(Formula,Beta1,Beta2),
                 !,
                 closed_branch([Beta1],[],[],Bs,Gs,Ls, Limite,Params,[Formula|Elaborate]),
                 closed_branch([Beta2],[],[],Bs,Gs,Ls, Limite,Params,[Formula|Elaborate]).
%gamma          
closed_branch([],[],[],[Formula|Gs],Ls,Limite,Params,Elaborate) :- 
                 is_gamma(Formula),
                 Params < Limite,
                 regola_gamma(Formula,Gammas,Limite,Params,Params1),
                 incrementa(Formula, Formula1, Params1),
                 append(Gs, [Formula1], Gs2),
                 !,
                 closed_branch(Gammas, [],[],[],Gs2,Ls, Limite,Params1,[Formula|Elaborate]). 

regola_alpha( A and B, A, B ).
regola_alpha( not ( A implies B ), A, not B ).
regola_alpha( not ( A or B ), not A, not B ).
regola_alpha( A sse B, A implies B, B implies A).


regola_beta( A or B, A, B ).
regola_beta( A implies B, not A, B ).
regola_beta( not ( A and B ), not A, not B ).
regola_beta( not ( A sse B ), not ( A implies B ), not ( B implies A ) ).


regola_delta(exists(X,Fbf),Fbf1,_,N):- N1 is N+1, instantiate( Fbf , X , N1 , Fbf1).
regola_delta(not forall(X,Fbf),not Fbf1,_,N):- N1 is N+1, instantiate( Fbf , X , N1 , Fbf1).


regola_gamma(forall(X, Fbf, N), Gammas, Limite, Params, Params1) :-
                            regola_gamma(Gammas, X, Fbf, N, N, Limite, Params, Params1).

regola_gamma(not exists(X, Fbf, N), Gammas, Limite, Params, Params1) :-
                            regola_gamma(Gammas, X, not Fbf, N, N, Limite, Params, Params1).

regola_gamma([Fbf1], X, Fbf, N, _, _, Params, Params1) :- N == Params,
                              !,
                              Params1 is Params + 1,
                              instantiate( Fbf , X , Params1 , Fbf1).

regola_gamma([Fbf1 | Gammas], X, Fbf, N, Next, _, Params, Params1) :- N < Params,
                              Next < Params,
                              Next1 is Next+1,
                              instantiate( Fbf , X , Next1 , Fbf1),
                              !,
                              regola_gamma(Gammas, X, Fbf, N, Next1, _, Params, Params1). 

regola_gamma([], _, _, N, Next, _, Params, Params) :- N < Params , Next == Params.



push_formula(not not Fbf,As,Ds,Bs,Gs,Ls,As1,Ds1,Bs1,Gs1,Ls1) :- !, push_formula(Fbf,As,Ds,Bs,Gs,Ls,As1,Ds1,Bs1,Gs1,Ls1).
push_formula(Fbf,As,Ds,Bs,Gs,Ls,[Fbf | As],Ds,Bs,Gs,Ls) :- is_alpha(Fbf), !. 
push_formula(Fbf,As,Ds,Bs,Gs,Ls,As,[Fbf | Ds],Bs,Gs,Ls) :- is_delta(Fbf), !. 
push_formula(Fbf,As,Ds,Bs,Gs,Ls,As,Ds,[Fbf | Bs],Gs,Ls) :- is_beta(Fbf), !.
push_formula(Fbf,As,Ds,Bs,Gs,Ls,As,Ds,Bs,[Fbf1 | Gs],Ls) :- is_fresh_gamma(Fbf, Fbf1), !.
push_formula(Fbf,As,Ds,Bs,Gs,Ls,As,Ds,Bs,[Fbf | Gs],Ls) :- is_gamma(Fbf), !. 
push_formula(Fbf,As,Ds,Bs,Gs,Ls,As,Ds,Bs,Gs,[Fbf | Ls]) :- atomo(Fbf), !.
push_formula(not Fbf,As,Ds,Bs,Gs,Ls,As,Ds,Bs,Gs,[not Fbf | Ls]) :- atomo(Fbf), !. 



chiude(not Fbf,_,_,Bs,_,_) :- is_alpha(Fbf), member(Fbf, Bs), !.
chiude(not Fbf,_,_,_,Gs,_) :- is_delta(Fbf), member(Fbf, Gs), !.
chiude(not Fbf,As,_,_,_,_) :- is_beta(Fbf), member(Fbf, As), !.
chiude(not Fbf,_,Ds,_,_,_) :- is_gamma(Fbf), member(Fbf, Ds), !.
chiude(not Fbf,_,_,_,_,Ls) :- atomo_ground(Fbf), member(Fbf, Ls), !.

chiude(Fbf,_,_,Bs,_,_) :- is_alpha(Fbf), member(not Fbf, Bs), !.
chiude(Fbf,_,_,_,Gs,_) :- is_delta(Fbf), member(not Fbf, Gs), !.
chiude(Fbf,As,_,_,_,_) :- is_beta(Fbf), member(not Fbf, As), !.
chiude(Fbf,_,Ds,_,_,_) :- is_gamma(Fbf), member(not Fbf, Ds), !.
chiude(Fbf,_,_,_,_,Ls) :- atomo_ground(Fbf), member(not Fbf, Ls), !.


% incrementa(Fbf, Fbf1) :- Fbf1 e' la formula di tipo gamma Fbf con il campo contatore N incrementato

incrementa(forall(X, Fbf, _), forall(X, Fbf, Params), Params).
incrementa(not exists(X, Fbf, _), not exists(X, Fbf, Params), Params).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Utilita'
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% maximum(X, Y, Z) :- Z e' il massimo tra X e Y

maximum(X,Y,X) :- X >= Y.
maximum(X,Y,Y) :- X < Y.


% delete(X, Lista, Lista1) :- Lista1 e' la lista risultante dalla cancellazione di X da Lista

delete(X, [X|Rest], Rest).
delete(X, [Y | Rest], [Y|Deleted]) :- !, delete(X, Rest, Deleted). 

nonmember(_, []).
nonmember(X, [Y|Ys]):- X \== Y, !, nonmember(X, Ys).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Utilita' per la stampa
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stampa_ramo(Fbf,As,Ds,Bs,Gs,Ls,Elaborate,Tipo) :-
    write('===========[RAMO '), write(Tipo), write(']==========='), nl,
    stampa_formule(Elaborate),
    stampa_formule(As),
    stampa_formule(Ds),
    stampa_formule(Bs),
    stampa_formule(Gs),
    stampa_formule(Ls),
    stampa_ultima_formula(Fbf),
    nl,
    write('==================================='), nl, nl.

stampa_formule( [] ).
stampa_formule( [Formula | Formulas] ) :- stampa_formule(Formulas), write(Formula), nl.

stampa_ultima_formula([]).
stampa_ultima_formula([Fbf]) :- write(Fbf), write(' XXX').
