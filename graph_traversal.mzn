int: nbNodes;
set of int: NODES = 1..nbNodes;
set of int: NODES0 = 0..nbNodes;
array[NODES, NODES] of NODES0 : graph;

include "globals.mzn";



% For an acyclic graph, from a starter node
function var int : count_paths(var NODES0: current_node, array[NODES, NODES] of NODES0 : graph) = 
      if current_node = 0 then 0
      else
        let {array[NODES] of var NODES0 : next_nodes = [graph[current_node, i] | i in NODES]; } in
        sum(node in next_nodes)(count_paths(node, graph))
      endif;
      
var int: nb_paths = count_paths(1, graph);
      
solve satisfy;