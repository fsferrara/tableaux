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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Predicato per verificare il tipo
%  delle formule ben formate
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_alpha(not not _).
is_alpha(_ and _).
is_alpha(not X) :- is_beta(X).

is_beta(_ or _).
is_beta(_ implies _).
is_beta(not X) :- is_alpha(X).

is_delta(exists( _ , _ )).
is_delta(not forall( _ , _ )).

is_fresh_gamma(forall( X , Y ), forall( X , Y , 0)).
is_fresh_gamma(not exists( X , Y ), not exists( X , Y , 0)).

is_gamma(forall( _ , _ , _ )).
is_gamma(not exists( _ , _ , _ )).



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
										
parametri_validi([Parametro | Tail]) :- compound(Parametro),
										Parametro =.. Tail1,
										!,
										parametri_validi(Tail1),
										parametri_validi(Tail).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Controllo formula ben formata
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fbf( X and Y ) :- !, fbf(X), fbf(Y).
fbf( X or Y ) :- !, fbf(X), fbf(Y).
fbf( X implies Y ) :-!,  fbf(X), fbf(Y).
fbf( forall(X,Y) ) :- !, atomic(X), fbf(Y).
fbf( exists(X,Y) ) :- !, atomic(X), fbf(Y).
fbf( not X ) :- !, fbf(X).
fbf( X ) :- atomo(X). 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Controllo parametri introdotti
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

massimo_parametro(Fbf, Tot) :- Fbf =.. [ _ | Args], massimo_intero(Args, Tot).

massimo_intero([], 0).
massimo_intero([Elem|Elems], Max) :- integer(Elem), !, massimo_intero(Elems, N), maximum(Elem, N, Max).
massimo_intero([Elem|Elems], Max) :- compound(Elem), !, 
									 massimo_parametro(Elem, N),
									 massimo_intero(Elems, N1),
									 maximum(N, N1, Max).
massimo_intero([Elem|Elems], Max) :- atom(Elem), massimo_intero(Elems, Max).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Instanziazione di fbf quantificate
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

instantiate( X and Y , Var , Par , X1 and Y1) :- !,  instantiate(X,Var,Par,X1), instantiate(Y,Var,Par,Y1).
instantiate( X or Y , Var , Par , X1 or Y1) :- !, instantiate(X,Var,Par,X1), instantiate(Y,Var,Par,Y1).
instantiate( X implies Y , Var , Par , X1 implies Y1) :- !, instantiate(X,Var,Par,X1), instantiate(Y,Var,Par,Y1).
instantiate( forall(X,Y),Var,Par,forall(X,Y1)) :- X \== Var, !,  instantiate(Y,Var,Par,Y1).
instantiate( forall(X,Y),Var,_,forall(X,Y)) :- X == Var, ! . %le occorrenze interne della variabile sono bounded nel quntificatore 
instantiate( exists(X,Y),Var,Par,exists(X,Y1)) :- X \== Var, !, instantiate(Y,Var,Par,Y1).
instantiate( exists(X,Y),Var,_,exists(X,Y)) :- X == Var,! .%le occorrenze interne della variabile sono bounded nel quntificatore 
instantiate( not X,Var,Par, not X1 ) :- !,  instantiate(X,Var,Par,X1).
instantiate( X,Var,Par,X1 ) :- atomo(X),!,  substitute_occurrences(X,Var,Par,X1).


substitute_occurrences(X,Var,Par,X1):- X =.. [Pred|Terms], substitute(Terms,Var,Par,Terms1),X1=.. [Pred|Terms1].

substitute([],_,_,[]).
substitute([Term | Tail],Var,Par,[Term1 | Tail1]) :- Term == Var,Term1 = Par,!, substitute(Tail,Var,Par,Tail1).
substitute([Term | Tail],Var,Par,[Term1 | Tail1]) :- Term \== Var,Term1 = Term, ! ,  substitute(Tail,Var,Par,Tail1).
substitute([CompTerm | Tail],Var,Par,[CompTerm1 | Tail1]) :- compound(CompTerm),substitute_occurrences(CompTerm,Var,Par,CompTerm1),substitute(Tail,Var,Par,Tail1).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Algoritmo per il calcolo del Tableau
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prova(Fbf) :- tclose(Fbf, 20).

tclose(Fbf, Limite) :- fbf(Fbf), massimo_parametro(Fbf, ParametroInizio), closed_branch([Fbf], Limite, ParametroInizio).

closed_branch([F1 | Ramo],Limite,_) :- member(not F1,Ramo),!, stampa_branch([F1|Ramo],Limite).
closed_branch([not F1 | Ramo],Limite,_) :- member(F1,Ramo),!, stampa_branch([not F1|Ramo],Limite). 
closed_branch([F1,F2 | Ramo],Limite,_) :- member(not F2,Ramo),!, stampa_branch([F1,F2|Ramo],Limite).
closed_branch([F1,not F2 | Ramo],Limite,_) :- member(F2,Ramo),!, stampa_branch([F1,not F2|Ramo],Limite).

closed_branch(Ramo,Limite,Params) :- member(Formula,Ramo),
								 is_alpha(Formula),
								 regola_alpha(Formula,Alpha1,Alpha2),
								 delete(Formula, Ramo, Ramo1),
								 !, 
								 closed_branch([Alpha1, Alpha2 | Ramo1], Limite,Params).
			
closed_branch(Ramo,Limite,Params) :- member(Formula,Ramo),
								 is_beta(Formula),
								 regola_beta(Formula,Beta1,Beta2),
								 delete(Formula, Ramo, Ramo1),
								 !, 
								 closed_branch([Beta1 | Ramo1], Limite,Params),
								 closed_branch([Beta2 | Ramo1], Limite,Params).

closed_branch(Ramo,Limite,Params) :- Params < Limite,
								 member(Formula,Ramo),
								 is_delta(Formula),
								 regola_delta(Formula,Delta1,Limite,Params),
								 delete(Formula, Ramo, Ramo1),
								 Params1 is Params + 1,
								 !, 
								 closed_branch([Delta1 | Ramo1], Limite,Params1).

closed_branch(Ramo,Limite,Params) :- member(Formula,Ramo),
								 is_fresh_gamma(Formula,Formula1),
								 delete(Formula, Ramo, Ramo1),
								 !, 
								 closed_branch([ Formula1 |Ramo1], Limite,Params).
								
closed_branch(Ramo,Limite,Params) :-  Params < Limite,
								 member(Formula,Ramo),
								 is_gamma(Formula),
								 regola_gamma(Formula,Gamma1,Limite,Params,Params1),
								 delete(Formula, Ramo, Ramo1),
								 incrementa(Formula, Formula1),
								 append(Ramo1, [Formula1], Ramo2),
								 !, 
								 closed_branch([Gamma1 | Ramo2], Limite,Params1). 

regola_alpha( A and B, A, B ).
regola_alpha( not not A, A, A ).
regola_alpha( not ( A implies B ), A, not B ).
regola_alpha( not ( A or B ), not A, not B ).
regola_alpha( A sse B, A implies B, B implies A).


regola_beta( A or B, A, B ).
regola_beta( A implies B, not A, B ).
regola_beta( not ( A and B ), not A, not B ).
regola_beta( not ( A sse B ), not ( A implies B ), not ( B implies A ) ).


regola_delta(exists(X,Fbf),Fbf1,_,N):- N1 is N+1, instantiate( Fbf , X , N1 , Fbf1).
regola_delta(not forall(X,Fbf),not Fbf1,_,N):- N1 is N+1, instantiate( Fbf , X , N1 , Fbf1).


regola_gamma(forall(X, Fbf, N), Fbf1, _, Params, Params1) :- N1 is N+1,
															 instantiate( Fbf , X , N1 , Fbf1),
															 maximum(Params,N1,Params1).
regola_gamma(not exists(X, Fbf, N), Fbf1, _, Params, Params1) :- N1 is N+1,
																 instantiate( Fbf , X , N1 , Fbf1),
																 maximum(Params,N1,Params1).


% incrementa(Fbf, Fbf1) :- Fbf1 e' la formula di tipo gamma Fbf con il campo contatore N incrementato

incrementa(forall(X, Fbf, N), forall(X, Fbf, N1)) :- N1 is N+1.
incrementa(not exists(X, Fbf, N), not exists(X, Fbf, N1)) :- N1 is N+1.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Utilita'
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% maximum(X, Y, Z) :- Z e' il massimo tra X e Y

maximum(X,Y,X) :- X >= Y, ! .
maximum(X,Y,Y) :- X < Y, !.


% delete (X, Lista, Lista1) :- Lista1 e' la lista risultante dalla cancellazione di X da Lista

delete(X, [X|Rest], Rest):- !.
delete(X, [Y | Rest], [Y|Deleted]) :- delete(X, Rest, Deleted). 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Utilita' per la stampa
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stampa_branch(Ramo,Limite) :- nl,write(Limite),nl,stampa_formule(Ramo),nl.

stampa_formule( [Formula] ) :- write(Formula).
stampa_formule( [Formula | Formulas] ) :- write(Formula), write(' , '), !, stampa_formule(Formulas).
 
