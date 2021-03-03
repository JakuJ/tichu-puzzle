% Domena

names([adam, cezary, eliza, hubert, irena, mateusz, natalia, sonia, tadeusz, urszula]).

player(X) :- names(N), member(X, N).

man(adam).
man(cezary).
man(hubert).
man(mateusz).
man(tadeusz).

woman(X) :- player(X), \+ man(X).

specjalne([smok, mah-jong, psy, feniks]).
sekwensy([od2, od3, od4, od5]).
kolory([czarny, zielony, niebieski, czerwony]).

% Funkcje pomocnicze

swap(P, X, Y) :- call(P, Y, X).

% Zadanie

miejsca(Pairs) :-
    names(Names),
    % jest 5 zestawów danych
    length(Pairs, 5),
    % kazdy ma dwie dane – imiona ludzi w parze
    maplist(swap(length, 2), Pairs),
    
    % Mateusz jest w parze z Ireną
    member([mateusz, irena], Pairs),
    % Nie zajęli ani 3 ani 5 miejsca
    member(MatIrIndex, [1, 2, 4]),
    nth1(MatIrIndex, Pairs, [mateusz, irena]),
    
    % zestawy muszą się sumować do wszystich graczy
    flatten(Pairs, Flattened),
    permutation(Names, Flattened),
    
    % Tadeusz jest w parze z kobietą
    member([tadeusz, A], Pairs),
    woman(A),
    % Adam jest w parze z mężczyzną
    member([adam, B], Pairs),
    man(B),

    % Natalia była wyżej od Cezarego
    nth1(IxNat, Pairs, [_, natalia]),
    nth1(IxCez, Pairs, [_, cezary]),
    IxNat < IxCez,
    % Sonia była wyżej od Tadeusza
    nth1(IxSon, Pairs, [_, sonia]),
    nth1(IxTad, Pairs, [tadeusz, _]),
    IxSon < IxTad,

    % W finale (dwie najlepsze pary) był jeden facet
    % "W zwycięskiej parze mieszanej to Eliza...""
    % Urszula jest wicemistrzynią
    [[SomeMan, eliza], [F3, F4] | _] = Pairs,
    man(SomeMan),
    (F3 = urszula; F4 = urszula)
    .

% ?- miejsca(X).
% X = [[hubert, eliza], [urszula, sonia], [tadeusz, natalia], [mateusz, irena], [adam, cezary]] ;
% false.

karcioszki(Data) :-
    sekwensy(Sekwensy),
    kolory(Kolory),
    specjalne(Specjalne),

    % są cztery zestawy danych
    [[hubert, HSpec, HC, HSek], [eliza, ESpec, EC, ESek], [urszula, USpec, UC, USek], [sonia, SSpec, SC, SSek]] = Data,
    
    % karty specjalne, sekwensy i ich kolory są unikatowe
    permutation(Specjalne, [HSpec, ESpec, USpec, SSpec]),
    permutation(Kolory, [HC, EC, UC, SC]),
    permutation(Sekwensy, [HSek, ESek, USek, SSek]),

    % Sekwensy posiadaczki feniksa i jedynego mężczyzny w finale nie zaczynały się od 4
    \+ member([_, feniks, _, od4], Data),
    HSek \= od4,

    % W zwycięskiej parze (..) to Eliza miała mah-jonga a ich sekwensy nie były niebieskie
    ESpec = mah-jong,
    EC \= niebieski,
    HC \= niebieski,

    % Najniższy sekwens nie był ani czerwony ani zielony
    \+ member([_, _, zielony, od2], Data),
    \+ member([_, _, czerwony, od2], Data),

    % Najwyszy sekwens był czarny
    member([_, _, czarny, od5], Data),

    % Psy miała osoba z czerwonym sekwensem
    member([_, psy, czerwony, _], Data),

    % Sekwens wicemistrzyni Urszuli był zielony
    UC = zielony.

% ?- karcioszki(X).
% X = [[hubert, psy, czerwony, od3], [eliza, mah-jong, czarny, od5], [urszula, smok, zielony, od4], [sonia, feniks, niebieski, od2]] ;
% false.
