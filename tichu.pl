% List the players of the tournament.
players([adam, cezary, eliza, hubert, irena, mateusz, natalia, sonia, tadeusz, urszula]).

% A player is one of the players.
player(X) :- players(P), member(X, P).

% List all men.
man(adam).
man(cezary).
man(hubert).
man(mateusz).
man(tadeusz).

% A woman is a player who is not a man.
woman(X) :-
    player(X),
    \+ man(X).

% Special Tichu cards that are mentioned in the puzzle.
special_cards([dragon, mah-jong, dog, phoenix]).

% Straight that were obtained in the final.
straights([from2, from3, from4, from5]).

% Possible colours of the straights.
colours([black, green, blue, red]).

% A helper function – applies an arity-2 predicate, swapping its arguments
swap(P, X, Y) :- call(P, Y, X).

% Find out the pairs and their standings in the tournament.
pairs_in_order(Pairs) :-
    % Bring all players into scope.
    players(Players),

    % There are 5 pairs in the tournament.
    length(Pairs, 5),
    maplist(swap(length, 2), Pairs),

    % Mateusz is paired with Irena.
    member([mateusz, irena], Pairs),

    % They were neither 3rd nor 5th, which means they were 1st, 2nd or 4th.
    member(MatIrIndex, [1, 2, 4]),
    nth1(MatIrIndex, Pairs, [mateusz, irena]),

    % All players must be present in the tournament.
    flatten(Pairs, Flattened),
    permutation(Players, Flattened),

    % Tadeusz is paired with a woman.
    member([tadeusz, A], Pairs),
    woman(A),

    % Adam is paired with another man.
    member([adam, B], Pairs),
    man(B),

    % Natalia finished higher than Cezary.
    nth1(IxNat, Pairs, [_, natalia]),
    nth1(IxCez, Pairs, [_, cezary]),
    IxNat < IxCez,

    % Sonia finished higher than Tadeusz.
    nth1(IxSon, Pairs, [_, sonia]),
    nth1(IxTad, Pairs, [tadeusz, _]),
    IxSon < IxTad,

    % In the final game (between the two best pairs), there was only one man.
    % Elisa was part of the the winning, mixed pair.
    [[SomeMan, eliza], [F3, F4] | _] = Pairs,
    man(SomeMan),

    % Urszula is one of the runner-ups.
    (F3 = urszula; F4 = urszula).

% Executing this query gives us only one possible arrangement:

% ?- pairs_in_order(X).
% X = [[hubert, eliza], [urszula, sonia], [tadeusz, natalia], [mateusz, irena], [adam, cezary]] ;
% false.

% Now we want to know which finalists had which cards.
players_cards(Data) :-
    % Bring card info into scope.
    straights(Straights),
    colours(Colours),
    special_cards(SpecialCards),

    % There are four finalists. Each has a special card and a straight from a given card and with a given colour.
    % We know the order of the finalists from running the previous query.
    [[hubert, HSpec, HC, HSek], [eliza, ESpec, EC, ESek], [urszula, USpec, UC, USek], [sonia, SSpec, SC, SSek]] = Data,

    % No two players can have the same special card, straight sequence or colour.
    permutation(SpecialCards, [HSpec, ESpec, USpec, SSpec]),
    permutation(Straights, [HSek, ESek, USek, SSek]),
    permutation(Colours, [HC, EC, UC, SC]),

    % The straights of the only man in the final game (Hubert) and the owner of the Phoenix didn't start with 4.
    \+ member([_, phoenix, _, from4], Data),
    HSek \= from4,

    % In the winning pair it was Eliza who had the Mah Jong, and their straights weren't blue.
    ESpec = mah-jong,
    EC \= blue,
    HC \= blue,

    % The lowest straight was neither red nor green.
    \+ member([_, _, red, from2], Data),
    \+ member([_, _, green, from2], Data),

    % The highest straight was black.
    member([_, _, black, from5], Data),

    % The Dog belongs to the person with the red straight.
    member([_, dog, red, _], Data),

    % Urszula's straight was green.
    UC = green.

% Executing this query gives us, yet again, only one answer.

% ?- players_cards(X).
% X = [[hubert, dog, red, from3], [eliza, mah-jong, black, from5], [urszula, dragon, green, from4], [sonia, phoenix, blue, from2]] ;
% false.
