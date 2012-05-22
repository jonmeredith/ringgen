%% -------------------------------------------------------------------
%%
%% riak_core: Core Riak Application
%%
%% Copyright (c) 2007-2010 Basho Technologies, Inc.  All Rights Reserved.
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% -------------------------------------------------------------------

%% More ring utilities
%%
%% ru:print_analysis(ru:sort_by_down_fbmax(ru:node_sensitivity(ru:make_ring([a, b, c, d, e, f, g, h, a, b, c, d, e, f, g, h]), 3, 2))).
%% ru:print_analysis(ru:sort_by_down_fbmax(ru:node_sensitivity(RM, 3, 2))).
%% ru:print_analysis(ru:sort_by_down_fbmax(ru:node_sensitivity(Ru, 3, 2))).
%% Ru:print_analysis(ru:sort_by_down_fbmax(ru:node_sensitivity(RT, 3, 2))).

-module(riak_core_claim_util).
-compile(export_all).

-record(load,    {node,    % Node name
                  num_pri, % Number of primaries
                  num_fb,  % Number of fallbacks
                  norm_fb}). % Normalised fallbacks - ratio of how many there are
                  
-record(failure, {down = [], % List of downed nodes
                  load = [], % List of #load{} records per up node
                  fbmin,
                  fbmean,
                  fbstddev,
                  fb10,
                  fb90,
                  fbmax}).
                  
%% -------------------------------------------------------------------
%% Ring statistics
%% -------------------------------------------------------------------

ring_stats(R, TN) ->
    violation_stats(R, TN) ++
        balance_stats(R) ++
        diversity_stats(R, TN).
    
%% TargetN violations
violation_stats(R, TN) ->
    [{violations, length(riak_core_ring_util:check_ring(R, TN))}].

balance_stats(R) ->
    Q = riak_core_ring:num_partitions(R),
    M = length(riak_core_ring:claiming_members(R)),
    AllOwners = riak_core_ring:all_owners(R),
    Counts = lists:foldl(fun({_,N},A) -> orddict:update_counter(N,1,A) end, [], AllOwners),
    Avg = Q / M,
    Balance = lists:sum([begin
                             Delta = trunc(Avg - Count),
                             Delta * Delta
                         end || {_, Count} <- Counts]),
    [{balance, Balance},
     {ownership, Counts}].

diversity_stats(R, TN) ->
    {_, Owners} = lists:unzip(riak_core_ring:all_owners(R)),
    {_, _AM, FixAM} = riak_core_claim_util:build(Owners),
    try
        [{diversity, riak_core_claim_util:score_am(FixAM, TN)}]
    catch
        _:empty_list ->
            [{diversity, 0}]
    end.
 
%% -------------------------------------------------------------------
%% Failure analysis
%% -------------------------------------------------------------------

print_failure_analysis(R, TargetN, NumFailures) ->
    ru:print_analysis(failure_analysis(R, TargetN, NumFailures)).

failure_analysis(R, TargetN, NumFailures) ->
    ru:sort_by_down_fbmax(ru:node_sensitivity(R, TargetN, NumFailures)).

worst_down(R, NVal, DownCombos) ->
    %% Work out all of the loads for each downcombo so ropt module can find the worst
    DownLoads = [ru:node_load(R, NVal, DownNodes) || DownNodes <- DownCombos],

    %% Find the node with the greatest norm_fb for the least downnodes
    %%  - first find the node name/worst norm_fb for each given load
    %%  - then work out the worst norm_fb for least down nodes
    WorstPerDownNodes = [worst_load(L) || L <- DownLoads],
    WorstOverAll = lists:sort(
                     [{NormFb, 1000000 - length(DownNodes), WorstNode, LeastNode, DownNodes} || 
                         {{NormFb, WorstNode, LeastNode}, DownNodes} <- 
                             lists:zip(WorstPerDownNodes, DownCombos)]),
    %% io:format("WorstOverAll\n~p\n", [WorstOverAll]),
    {_NormFB, _DownCount, WorstNode, LeastNode, DownNodes} = hd(lists:reverse(WorstOverAll)),
    {WorstNode, LeastNode, DownNodes}.

    %WorstLoads = hd(lists:reverse(lists:keysort(#load.norm_fb, AllLoads))),
    
%% Return worst affected node, 
worst_load(Load) ->
    ByNormFB = lists:keysort(#load.norm_fb, Load),
    [#load{node = WorstNode, norm_fb = WorstNormFB}|_] = ByNormFB,
    #load{node = LeastNode} = lists:last(ByNormFB),
    {WorstNormFB, WorstNode, LeastNode}.
    
%% For a given ring, with a list of downed nodes, compute
%% all preference lists then count up the number that
%% each node partipates in.
%%
%% [{node(), Primaries, Fallbacks, PortionOfKeySpace}]
%%
node_load(R, NVal, DownNodes) ->
    VL = vnode_load(R, NVal, DownNodes),
    TotFBs = lists:sum([NumFBs || {_N,_,NumFBs} <- VL]),
    [#load{node = N,
           num_pri = NumPris,
           num_fb = NumFBs,
           norm_fb = norm_fb(NumFBs, TotFBs)} || 
        {N, NumPris, NumFBs} <- VL].

vnode_load(R, NVal, DownNodes) ->
    UpNodes = riak_core_ring:all_members(R) -- DownNodes,
    Keys = [<<(I+1):160/integer>> ||
               {I,_Owner} <- riak_core_ring:all_owners(R)],
    %% NValParts = Nval * riak_core_ring:num_partitions(R),
    AllPLs = [riak_core_apl:get_apl_ann(Key, NVal, R, UpNodes) || Key <- Keys],
    FlatPLs = lists:flatten(AllPLs),
    [begin
         Pris = lists:usort([_Idx || {{_Idx, PN}, primary} <- FlatPLs, PN == N]),
         FBs = lists:usort([_Idx || {{_Idx, FN}, fallback} <- FlatPLs, FN == N]) -- Pris,
         {N, length(Pris), length(FBs)}
     end || N <- UpNodes].
    
down_overloads(R, NVal, DownCombos) ->
    [begin
         {CO, NOs} = down_overload(R, NVal, DownNodes),
         {DownNodes, CO, NOs}
     end || DownNodes <- DownCombos].

down_overload(R, NVal, DownNodes) ->
    NOs = node_overloads(vnode_load(R, NVal, DownNodes)),
    CO = lists:sum([NO || {NO,_N} <- NOs]),
    {CO, NOs}.

%% Compute an opqaue score for the ring - compute sum of squared overload
%% fallbacks
score_ring(O, NVal, Failures) when is_list(O) ->
    score_ring(make_ring(O), NVal, Failures);
score_ring(R, NVal, Failures) when is_integer(Failures) ->
    score_ring(R, NVal, down_combos(Failures, riak_core_ring:all_members(R)));
score_ring(R, NVal, DownCombos) ->
    %% Work out all of the loads for each downcombo so ropt module can find the worst
    lists:sum([begin
                   {CO, _NOs} = down_overload(R, NVal, DownNodes),
                   CO
               end || DownNodes <- DownCombos]).


%% Return a list of [{FBOVerload^2,node()}] - FBoverload is the number
%% of fallbacks above the mean.
node_overloads(VL) ->
    TotFBs = lists:sum([NumFB || {_Node, _NumPri, NumFB} <- VL]),
    NumUpNodes = length(VL),
    ExpFBs = (TotFBs + NumUpNodes - 1) div NumUpNodes, % expected fallbacks
    [{(NumFB - ExpFBs)*(NumFB - ExpFBs), N} || {N, _NumPri, NumFB} <- VL, NumFB > ExpFBs].


%% Compare two ring scores - lower scores are better
better_score(S1, S2) ->
    S1 < S2.

norm_fb(_, 0) ->
    0;
norm_fb(Num, Tot) ->
    Num / Tot.

analyze_load(Down, Load) ->
    FBStats = lists:foldl(fun(#load{num_fb = NumFB}, Acc) ->
                                  basho_stats_histogram:update(NumFB, Acc)
                          end,
                          basho_stats_histogram:new(1, 1024, 1024), Load),
    {FBMin, FBMean, FBMax, _FBVar, FBStdDev} = basho_stats_histogram:summary_stats(FBStats),
    FB10 = basho_stats_histogram:quantile(0.10, FBStats),
    FB90 = basho_stats_histogram:quantile(0.90, FBStats),
    #failure{down = Down, load = Load, fbmin = FBMin, fbmean = FBMean, fbstddev = FBStdDev,
             fb10 = FB10, fb90 = FB90, fbmax = FBMax}.

%% Mark each node down in turn and see how the spread of load is.
%%
%% Return a list of failures records, one for each case examined
node_sensitivity(R, NVal, Depth) ->
    Members = riak_core_ring:all_members(R),
    DownCombos = down_combos(Depth, Members),
    LoadCombos = [{Down, node_load(R, NVal, Down)} || Down <- DownCombos],
    [analyze_load(Down, Load) || {Down, Load} <- LoadCombos].

%%
%% Print the analysis on the console.
%% What is the best case result when we lose a node?  The vnodes that node was responsible
%% for are distributed evenly across the remaining nodes (probably proportionally)
%% 
%% FB expectation = sum(DownNodePartitions) / #UpNodes
%%
print_analysis(LoadAnalysis) ->
    print_analysis(standard_io, LoadAnalysis).
    
print_analysis(IoDev, LoadAnalysis) ->
    io:format(IoDev, " Min  Mean/  SD  10th  90th   Max  DownNodes/Worst\n", []),
    print_analysis1(IoDev, LoadAnalysis).

print_analysis1(_IoDev, []) ->
    ok;
print_analysis1(IoDev, [#failure{down = Down, load = Load, fbmin = FBMin,
                          fbmean = FBMean, fbstddev = FBStdDev,
                          fb10 = FB10, fb90 = FB90, fbmax = FBMax} | Rest]) ->
    %% Find the 3 worst FBmax
    Worst = 
        [{N,NumFB} || #load{node = N, num_fb = NumFB} <-
                          lists:sublist(lists:reverse(lists:keysort(#load.num_fb, Load)), 3)],
    
    io:format(IoDev, "~4b  ~4b/~4b  ~4b  ~4b  ~4b  ~w/~w\n", 
              [FBMin, toint(FBMean), toint(FBStdDev), toint(FB10), toint(FB90), FBMax, Down, Worst]),
    print_analysis1(IoDev, Rest).

toint(F) when is_number(F) ->
    round(F+0.5);
toint(X) ->
    X.


%% Sort by down ascending, then fbmax
sort_by_down_fbmax(Failures) ->
    Cmp = fun(#failure{down = DownA, fbmax = FBMaxA},
              #failure{down = DownB, fbmax = FBMaxB}) ->
                  %% length(DownA) =< length(DownB) andalso 
                  %%     FBMaxA >= FBMaxB andalso 
                  %%     DownA =< DownB
                  case {length(DownA), length(DownB)} of
                      {DownALen, DownBLen} when DownALen < DownBLen ->
                          true;
                      {DownALen, DownBLen} when DownALen > DownBLen ->
                          false;
                      _ ->
                          if
                              FBMaxA > FBMaxB ->
                                  true;
                              FBMaxA < FBMaxB ->
                                  false;
                              true ->
                                  DownA >= DownB
                          end
                  end
          end,
    lists:sort(Cmp, Failures).
    

%% Make a ring of size length(Nodes) ordering the nodes as given
make_ring(Nodes) ->
    R0 = riak_core_ring:fresh(length(Nodes), hd(Nodes)),
    Idxs = [I || {I,_} <- riak_core_ring:all_owners(R0)],
    NewOwners = lists:zip(Idxs, Nodes),
    R1 = lists:foldl(fun(N,R) ->
                             riak_core_ring:add_member(hd(Nodes), R, N)
                     end, R0, Nodes),
    lists:foldl(fun({I,N}, R) ->
                        riak_core_ring:transfer_node(I, N, R)
                end, R1, NewOwners).


%% For each ring
%%  compute stddev, max, min fallbacks as percentage of ring
score(InFn, OutFn, NVal, Failures) ->
    %% Open the files
    {ok, InH} = file:open(InFn, [read, read_ahead]),
    {ok, OutH} = file:open(OutFn, [write]),
    
    try
        score0(InH, OutH, NVal, Failures)
    after
        file:close(OutH),
        file:close(InH)
    end.

score0(InH, OutH, NVal, Failures) ->
    case file:read_line(InH) of
        eof ->
            ok;
        {ok, Line}->
            {ok, Toks, _} = erl_scan:string(Line ++ "."),
            {ok, L} = erl_parse:parse_term(Toks),
            io:format(OutH, "~w.\n", [ring_stats(L, NVal, Failures)]),
            score0(InH, OutH, NVal, Failures)
    end.

%% Take a necklace of node names, make it into a ring
%% work out fallbacks for each combination of failures
%% as percentage of downed paritions, so if
%% one node took over all responsibility for another
%% then it would be at 1
%%
%% There are Q*N partitions in all preference lists
ring_stats(L, NVal, Failures) ->
    R = make_ring(L),    
    DownCombos = down_combos(Failures, lists:usort(L)),
    Stats = load_stats(R, NVal, DownCombos),
    {basho_stats_sample:sdev(Stats), 
     basho_stats_sample:max(Stats), 
     basho_stats_sample:min(Stats),
     L}.

 
%% Work out load stats - returns a basho_stats_sample
load_stats(R, NVal, DownCombos) ->
    lists:foldl(fun(Down, Stats0) ->
                        Load = node_load(R, NVal, Down),
                        %% Load is a list of #load{} records - num_pri, num_fbs
                        NumFBs = [NumFB || #load{num_fb = NumFB} <- Load],
                        SumFBs = lists:sum(NumFBs),
                        NormFBs = [NumFB / SumFBs || NumFB <- NumFBs],
                        basho_stats_sample:update_all(NormFBs, Stats0)
                end, basho_stats_sample:new(), DownCombos).

%% -------------------------------------------------------------------
%% Permutations and combinations
%% -------------------------------------------------------------------

%% Permutations - number of ways to pick N out of K
num_perms(K, N) when K =< N ->
    fac(N) div (fac(N - K)).

%% Combinations - number of ways to combine N elements out of K
num_combs(K, N) when K =< N ->
    fac(N) div (K * fac(N - K)).

%% Factorials
fac(0) -> 
    1;
fac(1) ->
    1;
fac(N) when N > 1 ->
    N * fac(N-1).

%% Generate all permutations of list L
perm_gen([E]) ->
    [[E]];
perm_gen(L) ->
    lists:append([ begin
                       [ [X | Y] || Y <- perm_gen(lists:delete(X, L))]
                   end || X <- L]).
  
%% Pick all combinations of Depth nodes from the Mmebers list
%% 0 = []
%% 1 = [1], [2], [3]
%% 2 = [1,1], [1,2], [1,3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3]
down_combos(Depth, Members) ->
    down_combos(Depth, Members, []).

down_combos(0, _Members, Down) ->
    lists:usort([lists:usort(D) || D <- Down]);
down_combos(Depth, Members, []) ->
    down_combos(Depth - 1, Members, [[N] || N <- Members]);
down_combos(Depth, Members, Down) ->
    %% Add each of the members to the front of Down and iterate
    Down2 = [[N | D] || N <- Members, D <- Down],
    down_combos(Depth - 1, Members, Down2).


%% -------------------------------------------------------------------
%% Adjancency calculations
%% -------------------------------------------------------------------

adjacency(Owners) when is_list(Owners)->
    AL = adjacency_list(Owners),
    adjacency_matrix(AL).

%% For each node, work out the number of nodes between counting forward
%%
%% a,b,c,d,a,b,c,d,b,a,c,d,c,a,b,d
%%   
%%       Distance
%%        0   1   2   3   4
%% a->b   2
%% a->c
%% a->d
%% b->a
%% b->b
%% b->c
%% b->d
%%
%% What do we want this to be for perfect balance?  
%% one of each length?
%%
%% How do you could a,b,c,b - is that [0,2] or just 0?   Depends on the preflist
%% function.

%% Create a pair of node names and a list of counts
adjacency_list(Owners) ->
    adjacency_list(Owners, Owners++Owners, []).

adjacency_list([], _OwnersCycle, Acc) ->
    Acc;
adjacency_list([Node | Owners], [Node | OwnersCycle], Acc) ->
    adjacency_list(Owners, OwnersCycle, distances(Node, OwnersCycle, 0, Acc)).

distances(_Node, [], _, Distances) ->
    Distances;
distances(Node, [Node | _OwnerCycle], _, Distances) ->
    Distances;
distances(Node, [OtherNode | OwnerCycle], Distance, Distances) ->
    distances(Node, OwnerCycle, Distance + 1, 
              [{{Node, OtherNode}, Distance} | Distances]).


adjacency_matrix(AL) ->
    %% Make a count by distance of N1,N2
    NPairDists = lists:foldl(fun({NPair,D}, Acc) ->
                                    orddict:append_list(NPair, [D], Acc)
                            end, [], AL),
    [{NPair, count_distances(Ds)} || {NPair, Ds} <- NPairDists].

%% Fix the missing wraparound from the adjacency matrix - treat the end
%% of owners as wraping around to the start. Go back until out of entries in
%% M
fixup_am(Owners, AM) ->
    fixup_am(lists:usort(Owners), lists:reverse(Owners), Owners, AM).

fixup_am([], _ToFix, _Owners, AM) ->
    AM;
fixup_am(_M, [], _Owners, AM) ->
    AM;
fixup_am(M, [N | ToFix], Owners, AM) ->
    {Owners1, AM1} = prepend(M, N, Owners, AM),
    fixup_am(M -- [N], ToFix, Owners1, AM1).


%% Print adjacency matrix
square_am(AM) ->
    Nodes = lists:usort(lists:flatten([ [F,T] || {{F,T},_Ds} <- AM])),
    square_am(AM, Nodes).
    
square_am(AM, M) ->
    square_am(AM, M, fun(X) -> X end).

%% Print adjacency matrix
square_am(AM, M, Summary) ->
    %% Make sure adjacency matrix is fully populated
    AM1 = lists:foldl(fun(Pair,AM0) ->
                              orddict:append_list(Pair, [], AM0)
                      end, AM, [{F,T} || F <- M, T <- M]),
    [ begin
          [lists:sort(Summary(orddict:fetch({F,T}, AM1))) || T <- M]
      end || F <- M].


%% Take a list of distances: [4, 3, 0, 1, 1, 3, 3] and
%% create a list counting distance by position [1, 2, 0, 3, 1]
count_distances([]) ->
    [];
count_distances(Ds) ->
    MaxD = lists:max(Ds),
    PosCounts = lists:foldl(fun(D,Acc) ->
                                    orddict:update_counter(D, 1, Acc)
                            end, 
                            orddict:from_list([{D,0} || D <- lists:seq(0,MaxD)]),
                            Ds),
    [Count || {_Pos, Count} <- PosCounts].




%% -------------------------------------------------------------------
%% Balanced ring construction
%% -------------------------------------------------------------------

%% Generate a completion test function that makes sure all required
%% dbs are created
gen_complete_diverse(RequiredDs) ->
    fun(Owners, AM) ->
            OwnersLen = length(Owners),
            NextPow2 = next_pow2(OwnersLen),
            {met_required(Owners, AM, RequiredDs) andalso
                OwnersLen == NextPow2, NextPow2}
    end.

%% Generate until a fixed length has been hit
gen_complete_len(Len) ->
    fun(Owners, _AM) ->
            {length(Owners) == Len, Len}
    end.

%% M = list of node names
%% NVal = target nval
%% Required = list of required indices - should replace

construct(Complete, M, NVal) ->
    AM1 = lists:foldl(fun(Pair,AM0) ->
                              orddict:append_list(Pair, [], AM0)
                      end, [], [{F,T} || F <- M, T <- M, F /= T]),
    construct(Complete, M, [lists:last(M)], AM1, NVal).

                
construct(Complete, M, Owners, AM, NVal) ->
    %% Work out which pairs do not have the requiredDs
    case Complete(Owners, AM) of
        {true, _DesiredLen}->
            {ok, Owners, AM};
        {false, DesiredLen} ->
            %% Easy ones - restrict the eligible list to not include the N-1 
            %% previous nodes.  If within NVal-1 of possibly closing the ring
            %% then restrict in that direction as well.
            Eligible0 = M -- lists:sublist(Owners, NVal - 1),
            Eligible = case DesiredLen - length(Owners) of
                            Left when Left >= NVal ->
                                Eligible0; % At least Nval lest, no restriction
                            Left ->
                                Eligible0 -- lists:sublist(lists:reverse(Owners), Left)
                        end,
            case Eligible of
                [] ->
                    %% No eligible nodes - not enough to meet NVal, use any node
                    {Owners1, AM1} = prepend_next_owner(M, M, Owners, AM, NVal),
                    construct(Complete, M, Owners1, AM1, NVal);
                _ ->
                    %% NextOwner = next_owner(Eligible, Owners, AM, 0),
                    %% {Owners1, AM1} = prepend(M, NextOwner, Owners, AM),
                    {Owners1, AM1} = prepend_next_owner(M, Eligible, Owners, AM, NVal),
                    construct(Complete, M, Owners1, AM1, NVal)
            end
    end.

met_required(Owners, AM, RequiredDs) ->
    FixupAM = fixup_am(Owners, AM),
    case [Pair ||  {Pair, Ds} <- FixupAM, (RequiredDs -- Ds) /= [] ] of
        [] ->
            true;
        _ ->
            false
    end.

power_of_2(2) ->
    true;
power_of_2(N) ->
    case (N rem 2) of 
        0 ->
            power_of_2(N div 2);
        1 ->
            false
    end.

next_pow2(X) ->
    next_pow2(X, 2).

next_pow2(X, R) when X =< R ->
    R;
next_pow2(X, R) ->
    next_pow2(X, R*2).


%% Remove all of element R from L
removeall(R, L) ->
    [E || E <- L, not lists:member(E, R)].
           

%% Check if E is in first N elements of L, N may be greater than length(L)
nthmember(0, _E, _L) ->
    false;
nthmember(_N, _E, []) ->
    false;
nthmember(_N, E, [E|_T]) ->
    true;
nthmember(N, E, [_H|T]) ->
    nthmember(N - 1, E, T).

%% Randomize the order of the list
randomize([]) ->
    [];
randomize(L) ->
    randomize(length(L), L, []).

randomize(Count, L) when Count =< length(L) ->
    randomize(Count, L, []).

randomize(1, [E|_], Acc) ->
    [E | Acc];
randomize(Len, L, Acc) ->
    Pos = crypto:rand_uniform(0, length(L)),
    {L1, [E | L2]} = lists:split(Pos, L),
    randomize(Len - 1, L1 ++ L2, [E | Acc]).


%% For each eligible, work out which node improves diversity the most
%% Take the AM scores and cap by TargetN and find the node that
%% improves the RMS 
prepend_next_owner(M, [Node], Owners, AM, _TN) -> % If only one node, not a lot of decisions to make
    prepend(M, Node, Owners, AM);
prepend_next_owner(M, Eligible, Owners, AM, TN) ->
    {_BestScore, Owners2, AM2} = 
        lists:foldl(fun(Node, {RunningScore, _RunningO, _RunningAM}=Acc) ->
                            {Owners1, AM1} = prepend(M, Node, Owners, AM),
                            case score_am(AM1, TN) of
                                BetterScore when BetterScore < RunningScore ->
                                    {BetterScore, Owners1, AM1};
                                _ ->
                                Acc
                            end
                    end, {undefined, undefined, undefined}, Eligible),
    {Owners2, AM2}.


%% Work out the best next From
%% Find a {From,To} pair that will add a new distance
%% between the two pair.  For each distance, look if there
%% is a new {[Eligible],To} pair that adds a new D.
next_owner(Eligible, [], _AM, _D) ->
    io:format("next_form got stuck - using first eligible node\n"),
    hd(Eligible);
next_owner(Eligible, [To | Owners], AM, D) ->
    case [F || {{F, T}, Ds} <- AM,
               not lists:member(D, Ds),
               lists:member(F, Eligible),
               T == To ] of
        [] ->
            next_owner(Eligible, Owners, AM, D + 1);
        Candidates ->
            Next = lowest_freq_owner(Candidates, Owners),
            io:format("Chose ~p from ~p to prepend to ~p\n", [Next, Candidates, Owners]),
            Next
    end.

%% Rank the candidates by ownership, least first
rank_candidates_by_ownership(Candidates, Owners) ->
    Cs = ordsets:from_list(Candidates),
    Freqs0 = orddict:from_list([{N,0} || N <- Candidates]),
    Freqs = lists:foldl(fun(N,A) -> 
                                case ordsets:is_element(N, Cs) of
                                    true ->
                                        orddict:update_counter(N,1,A);
                                    _ ->
                                        A
                                end
                        end, Freqs0, Owners),    
    [Node || {Node, _Count} <- lists:keysort(2, Freqs)].

lowest_freq_owner(Candidates, Owners) ->
    hd(rank_candidates_by_ownership(Candidates, Owners)).
        
build(Owners) ->
    build(lists:usort(Owners), lists:reverse(Owners), [], []).

build(_M, [], Owners, AM) ->
    {Owners, AM, fixup_am(Owners, AM)};
build(M, [N|Rest], Owners, AM) ->
    {Owners1, AM1} = prepend(M, N, Owners, AM),
    %% io:format("Adding ~p to ~w\n~p\n", 
    %%           [N, Owners, square_am(fixup_am(Owners1, AM1), M)]),
    build(M, Rest, Owners1, AM1).


count(L) ->
    lists:foldl(fun(E,A) -> orddict:update_counter(E, 1, A) end, [], L).
                         

%% Prepend N to the front of Owners, and update AM
prepend(M, N, Owners, AM) ->
    Ds = distances2(M -- [N], Owners),
    AM2 = lists:foldl(fun({T,D},AM1) ->
                              orddict:append_list({N,T},[D],AM1)
                      end, AM, Ds),
    {[N | Owners], AM2}.

%% Calculate the distances to each of the M nodes until
%% a distance for each has been found.
distances2(M, Owners) ->
    distances2(M, Owners, 0, []).

distances2([], _Owners, _D, Acc) ->
    Acc;
distances2(_M, [], _D, Acc) ->
    Acc;
distances2(M, [T | Owners], D, Acc) ->
    case lists:member(T, M) of
        true ->
            distances2(M -- [T], Owners, D + 1, [{T, D} | Acc]);
        false ->
            distances2(M, Owners, D + 1, Acc)
    end.


%% For each pair, get the count of distances < NVal
score_am(AM, NVal) ->
    Cs = lists:flatten(
           [begin
                [C || {D,C} <- count(Ds), D < NVal]
            end || {_Pair,Ds} <- AM]),
    rms(Cs).

rms([]) ->
    throw(empty_list);
rms(L) ->
    Mean = lists:sum(L) / length(L),
    lists:sum([(Mean - E) * (Mean - E) || E <- L]).
    
 
%% Replace element N of L with E    
%%  0 = replace head, length(L) replace tail
replace(N, E, L) ->
    {L1, L2} = lists:split(N, L),
    case L2 of
        [] ->
            L1 ++ [E];
        _ ->
            L1 ++ [E] ++ tl(L2)
    end.

score_replacements(Indices, Node, Owners, NVal) when is_list(Indices) ->
    O2 = lists:foldl(fun(Pos, O0) ->
                             replace(Pos, Node, O0)
                     end, Owners, Indices),
    {_, _AM, FixAM} = build(O2),
    {O2, score_am(FixAM, NVal)}.

%% score_replacement(Pos, Node, Owners, NVal) ->
%%     O2 = replace(Pos, Node, Owners),
%%     {_, _AM, FixAM} = build(O2),
%%     {score_am(FixAM, NVal), O2}.


    
%% 
%% Ring generation
%% 

        
%% S = number of nodes
%% Q = number of partitions
%% 
canonicals(Q, S) ->
    ets:new(canonicals, [named_table, private, ordered_set]),
    ets:new(rings, [named_table, private, ordered_set]),

    try
        %% Generate all rings
        Names = names(S),
        Rings = gen(Q, Names),
                
        %% For each ring
        [update_canonicals(L, Names) || L <- Rings],
        
        %% Dump them out
        dump("rgtest")
    after
        ets:delete(canonicals),
        ets:delete(rings)
    end.


update_canonicals(L, Names) ->
    %%  Check if canonical ring already exists
    case ets:lookup(rings, L) of
        [] ->
            %% First time this ring has been seen
            %% Add it to canonicals
            true = ets:insert(canonicals, {L}),

            %% Add all mutations to rings
            Subs = substitutions(L, Names),
            [ets:insert(rings, [{R, L} || R <- rotations(S)]) || S <- Subs];
        _ ->
            %% Already generated it, do nothing
            ok
    end.

%% Generate all rotated versions of an ownership list
rotations([H|T] = L) -> 
    rotations(length(L) - 1, T ++ [H], [L]).

rotations(0, _, Acc) ->
    lists:reverse(Acc);
rotations(Rem, [H|T] = L, Acc) ->
    rotations(Rem - 1, T ++ [H], [L | Acc]).

%% Generate a list with each possible substitution for a name                             [A,B,C]
%% substitutions([A, A, B, C], [A, B, C]) == [[A, A, C, B], % A->A, B->C, C->B ==[A,B,C]->[A,C,B]
%%                                            [B, B, A, C], % A->B, B->A, C->C ==[A,B,C]->[B,A,C]
%%                                            [B, B, C, A], % A->B, B->C, C->A ==[A,B,C]->[B,C,A]
%%                                            [C, C, B, A], % A->C, B->B, C->A ==[A,B,C]->[C,B,A]
%%                                            [C, C, A, B]] % A->C, B->A, C->B ==[A,B,C]->[C,A,B]
%% 
substitutions(L, Names) ->
    PNames = perms(Names),
    [substitute(Names, P, L) || P <- PNames].

%% Replace elements in L looking up Name and replacing with element in Mapping
substitute(Names, Mapping, L) ->
    D = dict:from_list(lists:zip(Names, Mapping)),
    [dict:fetch(E, D) || E <- L].

%% %% Generate all the permutations of list L using Steinhause-Johnson-Trotter
%% perms(L) ->
%%     for i = 1..n
%%       let xi be the place i is placed in permutationt pi
%%         if the order of the numbers from 1 to i-1 defines an even permutation,
%%            yi = xi -1,
%%         else
%%            yi = xi + 1
%%         find the largest number i for which yi defines a valid position in permutation
%%            pi that contains a number smaller than i,
%%             swap the values in position xi and yi
    

perms([H|T]) ->
    perms(T, [[H]]).

perms([], Acc) ->
    Acc;
perms([H | T], Acc) ->
    %% Make a list by inserting H into each position of Acc
    perms(T,  lists:append([insert(H, A0) || A0 <- Acc])).

insert(E, L) ->
    insert(E, [], L, []).

insert(E, L1, [], Acc) ->
    [L1 ++ [E] | Acc];
insert(E, L1, [H2|T2] = L2, Acc) ->
    insert(E, L1 ++ [H2], T2,  [L1 ++ [E] ++ L2 | Acc]).
    

%% Create node name atoms - just use a, b, c for now
names(S) ->
    [name(I) || I <- lists:seq(0, S-1)].

name(I) ->
    name(I, []).

name(I, Acc) when I < 26->
    list_to_atom([($0 + I) | Acc]);
name(I, Acc) ->
    name((I div 26) - 1, [($0 + (I rem 26)) | Acc]).



%% Generate every possible ring of size Q with the given names
gen(Q, Names) ->
    %[lists:duplicate(Q, hd(Names))].
    gen(Q - 1, Names, [[N] || N <- Names]).

%% Add each of the names to the front of the existing acc
gen(0, _Names, Acc) ->
    Acc;
gen(Q, Names, Acc) ->
    Acc1 = lists:append([[[N | A] || A <- Acc] || N <- Names]),
    gen(Q - 1, Names, Acc1).
    

%% Dump the ETS tables rings to a file
dump(Basename) ->
    io:format("Canonicals: ~p\n", [proplists:get_value(size, ets:info(canonicals))]),
    io:format("Rings: ~p\n", [proplists:get_value(size, ets:info(rings))]),
    {ok, FC} = file:open(Basename ++ ".canonical", [write]),
    ets:foldl(fun({L}, _Acc) -> 
                      begin 
                          io:format(FC, "~w\n", [L]),
                          io:format("~w\n", [L])
                      end
              end, undefined, canonicals),
    file:close(FC),
    {ok, FR} = file:open(Basename ++ ".rings", [write]),
    ets:foldl(fun({L, C}, _Acc) -> io:format(FR, "~w <- ~w ~s\n",
                                             [L, C, case L == C of true -> "canonical"; _ -> "" end])
              end, undefined, rings),
    file:close(FR),
    ok.
    

%% Work out the valid canonical rings, will not detect duplicates
%% through renaming
valid_canonicals(Q, S, N) ->
    Names = names(S),    
    First = ownership(Q, Names),
    Name = lists:flatten(io_lib:format("valid_q~p_s~p_n~p.txt", [Q, S, N])),
    {ok, Fh} = file:open(Name, [write]),
    try
        valid_canonicals(Fh, First, cycle(First), N, analyze(Fh, First, N, {0, 0}))
    after
        file:close(Fh)
    end.

valid_canonicals(_Fh, First, First, _N, {Valid, Invalid}) ->
    {Valid, Invalid};
valid_canonicals(Fh, First, Ownership, N, Acc) ->
    valid_canonicals(Fh, First, cycle(Ownership), N, analyze(Fh, Ownership, N, Acc)).

analyze(Fh, Ownership, N, {Valid, Invalid}) ->
    case valid_preflists(Ownership, N) of
        false ->
            {Valid, Invalid + 1};
        _PLs ->
            io:format(Fh, "~w\n", [Ownership]),
            {Valid + 1, Invalid}
    end.


%% Mutate the list until you get back to the start
necklaces(L) ->
    Ls = lists:sort(L),
    %io:format("~w\n", [Ls]),
    necklaces(cycle(Ls), Ls, 0).

necklaces(S, S, C) ->
    C;
necklaces(L, S, C) ->
    io:format("~w\n", [L]),
    necklaces(cycle(L), S, C+1).


%% From Aaron Williams PhD thesis
%% http://webhome.csc.uvic.ca/~haron/
%%
%% The first symbol a is shifted to the right until it passes over consecutive 
%% symbols b c with b < c. 
%%
%% If a > b, then a is inserted after b; otherwise, if a <= b, then a is inserted after c. 
%%
%% (If there is no such b c then a is shifted until it passes over the rightmost symbol.)
%%
cycle([A|T]) ->
    case shift(T) of
        none ->
            T++[A];
        {Prefix, [B, C | Rest]} ->
            case A > B of
                true ->
                    Prefix ++ [B, A, C | Rest];
                _ ->
                    Prefix ++ [B, C, A | Rest]
            end
    end.

shift(T) ->
    shift([], T).

shift(_Prefix, [_B]) ->
    none;
shift(Prefix, [B, C |_]=L) when B < C->
    {lists:reverse(Prefix), L};
shift(Prefix, [B | Rest]) ->
    shift([B | Prefix], Rest).



%%
%% Build all valid preference lists for a ring, if any preflist does not
%% have unique nodes then return false.
%% 
valid_preflists(L, N) ->
    valid_preflists(L ++ lists:sublist(L, N-1), N, []).

valid_preflists(L, N, Acc) when length(L) < N ->
    Acc;
valid_preflists(L, N, Acc) ->
    PL = lists:sublist(L, N),
    case length(lists:usort(PL)) of
        N ->
            valid_preflists(tl(L), N, [PL | Acc]);
        _ ->
            false
    end.
    
    
ownership(Q, Names) ->
    Base = Q div length(Names),
    Boost = Q rem length(Names),
    ownership(Names, Boost, Base, []).

ownership([], _, _, Acc) ->
    lists:reverse(lists:flatten(Acc));
ownership([N|Rest], Boost, Base, Acc) ->
    case Boost > 0 of
        true ->
            ownership(Rest, Boost - 1, Base, [lists:duplicate(Base+1, N) | Acc]);
        _ ->
            ownership(Rest, 0, Base, [lists:duplicate(Base, N) | Acc])
    end.

    
                           
%% Analyze load on nodes under failure

failure_load(L, N, Down) ->
    failure_load(L ++ [$$], N, [$$ | Down], []).

%% Stop on the sentinel
failure_load([$$ | _], _N, _Down, FailLoad) ->
    FailLoad;
failure_load(L, N, Down, FailLoad0) ->
    {Pris,FBs} = lists:split(N, upnodes(L, [$$])),
    UpPris = upnodes(Pris, Down),
    FailLoad = case N - length(UpPris) of
                   0 -> % no down nodes
                       io:format("~w\n", [UpPris]),
                       FailLoad0;
                   NumFBs ->
                       %% Work out which nodes will be fallbacks and update
                       UpFBs = lists:sublist(upnodes(FBs, Down), NumFBs),
                       io:format("~w -> ~w / ~w\n", [Pris, UpPris, UpFBs]),
                       lists:foldl(fun(FB,FL) ->
                                           orddict:update_counter(FB, 1, FL)
                                   end, FailLoad0, UpFBs)
               end,
    failure_load(tl(L) ++ [hd(L)], N, Down, FailLoad).

upnodes(Nodes, Down) ->
    lists:filter(fun(X) -> not lists:member(X, Down) end, Nodes).



%% Assemble a ring from a list of possible preflists.
%% [[A,B,C],[]....]
%%
%% 
assemble(N, PLs) ->
    try
        assemble(N, hd(PLs), tl(PLs))
    catch
        _:{found, L} ->
            L
    end.     

assemble(_N, L, []) ->
    %% io:format("Found ~w\n", [L]),               
    throw({found, L});
assemble(N, L, PLs) ->
    %% Prefix is the last N nodes in L
    {_, Prefix} = lists:split(length(L) - N, L),

    %% Find PLs with a prefix of the last N nodes of L

    case[PL || PL <- PLs, lists:prefix(Prefix, PL)] of
        [] ->
            %io:format("Stuck at ~w with ~p PLs remaining\n", [L, length(PLs)]),
            [];
        
        Candidates ->
            %% io:format("~w - prefix ~p has ~p / ~p candidates\n", 
            %%           [L, Prefix, length(Candidates), length(PLs)]),
            %% For each, remove from PLs and append to L and recursively generate
            [begin
                 %%io:format("Testing ~w ++ ~w\n", [L, C]),
                 {_, Suffix} = lists:split(N, C),
                 assemble(N, L++Suffix, lists:delete(C, PLs))
             end || C <- Candidates]
    end.
