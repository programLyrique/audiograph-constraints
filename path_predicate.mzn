int: nbNodes;
set of int: NODES = 1..nbNodes;
set of int: NODES0 = 0..nbNodes;
array[NODES, NODES] of NODES0 : graph;

array[NODES, NODES] of var bool: inci_graph;

constraint forall(n1, n2 in NODES)(inci_graph[n1,n2] <-> exists(j in NODES)(graph[n1, j] = n2));

include "globals.mzn";

predicate is_path_mat(array[NODES] of var NODES0: path) = % Incidence matrix
  let {var 2..nbNodes: end; } in
  forall(j in end+1..nbNodes)(path[j] = 0) /\
  forall(i in 2..end)(inci_graph[path[i-1], path[i]]) ;
  
array[NODES] of var NODES0 : paths;
%No cycles
constraint alldifferent_except_0(paths);

constraint forall(i in NODES)(exists(j in NODES0)(paths[i] = j));
% 0 are at the end
constraint forall(i in NODES)( paths[i] = 0 -> forall(j in i..nbNodes)(paths[j] = 0));

constraint is_path_mat(paths);


function var int : path_length(array[NODES] of var NODES0: path) = 
   sum(i in NODES)(paths[i] != 0);
   

% Find a path of length 2
constraint path_length(paths) = 3;

output ["paths = \(paths);\n"];
      
solve satisfy;