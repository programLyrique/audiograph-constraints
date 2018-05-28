int: nbNodes;
set of int: NODES = 1..nbNodes;
set of int: NODES0 = 0..nbNodes;
array[NODES, NODES] of NODES0 : graph;

include "globals.mzn";

% Inputs and outputs
var set of NODES: inputs;
var set of NODES: outputs;

predicate inputs(var set of NODES: inputs, array[NODES, NODES] of NODES0 : graph) = 
  forall(n1, i in NODES, n2 in inputs)(graph[n1, i] != n2);
predicate outputs(var set of NODES: outputs, array[NODES, NODES] of NODES0 : graph) = 
  forall(n1 in outputs, i in NODES)(graph[n1, i] = 0);
  
constraint inputs(inputs, graph);
constraint outputs(outputs, graph);

% Incidence matrix
array[NODES, NODES] of var 0..1 : mat_graph;
predicate adj_mat_graph(array[NODES, NODES] of NODES0 : graph, array[NODES, NODES] of var 0..1 : mat_graph) = 
    forall(n1, n2, i in NODES)
               (mat_graph[n1, n2] = 1 <-> exists(i in NODES)(graph[n1, i] = n2));
constraint adj_mat_graph(graph, mat_graph);   

solve satisfy;


output ["inputs = \(inputs);\n",
        "outputs = \(outputs);\n",
        "mat_graph = \(mat_graph);\n"];