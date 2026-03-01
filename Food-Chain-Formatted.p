tff(species_type,type,
    species: $tType ).

tff(foodlink_type,type,
    foodlink: $tType ).

tff(foodchain_type,type,
    foodchain: $tType ).

tff(is_primary_producer_type,type,
    is_primary_producer: species > $o ).

tff(is_apex_predator_type,type,
    is_apex_predator: species > $o ).

tff(is_complete_foodchain_type,type,
    is_complete_foodchain: foodchain > $o ).

tff(does_eat_type,type,
    does_eat: ( species * species ) > $o ).

tff(does_depend_upon_type,type,
    does_depend_upon: ( species * species ) > $o ).

tff(eater_of_type,type,
    eater_of: foodlink > species ).

tff(eaten_of_type,type,
    eaten_of: foodlink > species ).

tff(start_of_type,type,
    start_of: foodchain > species ).

tff(end_of_type,type,
    end_of: foodchain > species ).


tff(eater_eats_eaten,axiom,
    ! [L: foodlink] : does_eat(eater_of(L),eaten_of(L)) ).

tff(no_cannibals,axiom,
    ! [L: foodlink] : ( eater_of(L) != eaten_of(L) ) ).

tff(eats_or_eaten,axiom,
    ! [S: species] :
    ? [S2: species] :
      ( does_eat(S,S2)
      | does_eat(S2,S) ) ).

tff(primary_producers_rule,axiom,
    ! [S: species] :
      ( is_primary_producer(S)
    <=> ~ ? [S2: species] : does_eat(S,S2) ) ).

tff(primary_producers_eat_nobody,conjecture,
    ! [S: species] :
      ( is_primary_producer(S)
     => ~ ? [L: foodlink] : ( eater_of(L) = S ) ) ).

tff(primary_producers_are_eaten,conjecture,
    ! [S: species] :
      ( is_primary_producer(S)
     => ? [S2: species] : does_eat(S2,S) ) ).

tff(not_primary_eats_someone,conjecture,
    ! [S: species] :
      ( ~ is_primary_producer(S)
     => ? [S2: species] : does_eat(S,S2) ) ).


tff(apex_predator_rule,axiom,
    ! [S: species] :
      ( is_apex_predator(S)
    <=> ~ ? [S2: species] : does_eat(S2,S) ) ).

tff(apex_not_eaten,conjecture,
    ! [S: species] :
      ( is_apex_predator(S)
     => ~ ? [L: foodlink] : ( eaten_of(L) = S ) ) ).

tff(apex_eats_someone,conjecture,
    ! [S: species] :
      ( is_apex_predator(S)
     => ? [S2: species] : does_eat(S,S2) ) ).

tff(non_apex_are_eaten,conjecture,
    ! [S: species] :
      ( ~ is_apex_predator(S)
     => ? [S2: species] : does_eat(S2,S) ) ).


tff(food_chain_rule,axiom,
    ! [C: foodchain] :
    ? [L: foodlink] :
      ( ( start_of(C) = eaten_of(L) )
      & ( ( eater_of(L) = end_of(C) )
      <~> ? [C2: foodchain] :
            ( ( start_of(C2) = eater_of(L) )
            & ( end_of(C2) = end_of(C) ) ) ) ) ).

tff(no_death_spirals,axiom,
    ! [C: foodchain] : ( start_of(C) != end_of(C) ) ).

tff(complete_foodchain_rule,axiom,
    ! [C: foodchain] :
      ( is_complete_foodchain(C)
     => ( is_primary_producer(start_of(C))
        & is_apex_predator(end_of(C)) ) ) ).

tff(all_species_in_a_complete_chain,axiom,
    ! [S: species] :
    ? [C: foodchain] :
      ( is_complete_foodchain(C)
      & ( ( S = start_of(C) )
        | ( S = end_of(C) )
        | ? [C1: foodchain,C2: foodchain] :
            ( ~ is_complete_foodchain(C1)
            & ~ is_complete_foodchain(C2)
            & ( start_of(C1) = start_of(C) )
            & ( end_of(C1) = S )
            & ( start_of(C2) = S )
            & ( end_of(C2) = end_of(C) ) ) ) ) ).

tff(start_does_not_eat_end,conjecture,
    ! [C: foodchain] :
      ( is_complete_foodchain(C)
     => ~ does_eat(start_of(C),end_of(C)) ) ).

tff(regular_species_have_chains,conjecture,
    ! [S: species] :
      ( ( ~ is_primary_producer(S)
        & ~ is_apex_predator(S) )
     => ? [C1: foodchain,C2: foodchain] :
          ( is_primary_producer(start_of(C1))
          & ( end_of(C1) = S )
          & ( start_of(C2) = S )
          & is_apex_predator(end_of(C2)) ) ) ).


tff(depends_rule,axiom,
    ! [S1: species,S2: species] :
      ( does_depend_upon(S1,S2)
    <=> ? [C: foodchain] :
          ( ( start_of(C) = S2 )
          & ( end_of(C) = S1 ) ) ) ).

tff(non_apex_must_have_dependent,conjecture,
    ! [S: species] :
      ( ~ is_apex_predator(S)
     => ? [A: species] :
          ( is_apex_predator(A)
          & does_depend_upon(A,S) ) ) ).

tff(apex_depends_rule,conjecture,
    ! [A: species,P: species,C: foodchain] :
      ( ( is_apex_predator(A)
        & is_primary_producer(P)
        & is_complete_foodchain(C)
        & ( end_of(C) = A )
        & ( start_of(C) = P ) )
     => does_depend_upon(A,P) ) ).

