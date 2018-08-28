/* A model of an audiograph */

int : nbTasks;
set of int : TASKS = 1..nbTasks;
array[TASKS, TASKS] of bool : audiograph;
int : deadline;
int : samplerate;

var set of TASKS: inputs;
var set of TASKS: outputs;
constraint forall(t1 in TASKS, t2 in inputs)(audiograph[t1,t2] = false);
constraint forall(t1 in outputs, t2 in TASKS)(audiograph[t1,t2] = false);

include "globals.mzn";

set of int: TASKS0 = 0..nbTasks;

% int : max_edges = nbTasks * (nbTasks - 1);% Self-loops are forbidden (and there are no loops on the graph)
% set of int: EDGES = 1..max_edges;
% array[EDGES, 1..2] of var TASKS0 : edge_graph;
% constraint alldifferent_except_0([edge_graph[i,j] | i in 1..max_edges, j in 1..2]);
% % Channeling the two graph representations
% constraint forall(t1, t2 in TASKS, i in 1..max_edges)(audiograph[t1,t2] <-> edge_graph[i, 1] = t1 /\ edge_graph[i,2] = t2);
% % Finding all paths between inputs and outputs

/******************************
 ** Paths in a graph 
 *****************************/
array[TASKS] of TASKS0 : paths;% Acyclic so any path uses at most the number of nodes in the graph

constraint alldifferent_except_0(paths);% A path is made of different tasks (no cycles).
constraint forall(i in TASKS)( paths[i] = 0 -> forall(j in i..nbTasks)(paths[j] = 0)); % We put the zeros at the end
predicate is_path_mat(array[TASKS] of var TASKS0: path) = % with incidence matrix 
  let {var 2..nbTasks: end; } in
  forall(j in end+1..nbTasks)(path[j] = 0) /\
  forall(i in 2..end)(audiograph[path[i-1], path[i]]) ;
constraint is_path_mat(paths);%The nodes in order in the array form a path
  


        
/******************************
 ** Resamplers
 *****************************/
enum RESAMPLER;
RESAMPLER: NoResampler;
array[RESAMPLER] of 0..100 : quality;% Compute it using the formula
array[RESAMPLER] of int : resampler_factor;% +2 = x 2 and -2 = / 2
array[RESAMPLER] of int : resampler_duration;
int : max_duration = max(resampler_duration);
array[TASKS,TASKS] of var RESAMPLER : resampler; 
int : max_resamplers = nbTasks * (nbTasks - 1);
var int : nb_resamplers = sum(t1,t2 in TASKS)(resampler[t1,t2] != NoResampler);
set of int : MAX_DUR = 0..max_duration;
array[1..max_resamplers] of var MAX_DUR : resampler_dur; % 0 denotes no resampler
array[1..max_resamplers] of var opt TIME : resampler_start;

predicate array_opt_eq(array[int] of var opt int : a1, array[int] of var opt int : a2) = 
    length(a1) = length(a2) /\
    forall(i in index_set(a1))(int_eq(a1[i], a2[i]));

% To get an array of start times and duration for the resamplers
predicate active_resamplers_start_duration(array[TASKS,TASKS] of var RESAMPLER : resampl, 
                                           array[1..max_resamplers] of var MAX_DUR : duration_r,
                                           array[1..max_resamplers] of var opt TIME : start_r,
                                           array[TASKS] of int : duration_t,
                                           array[TASKS] of var TIME : start_t) = 
         let {array[TASKS, TASKS] of var MAX_DUR : dur; array[TASKS, TASKS] of var TIME : sta; } in
         forall(t1, t2 in TASKS where resampl[t1,t2] != NoResampler)
                       (sta[t1,t2] = start_t[t1] + duration_t[t1]  %Start at the end of t1
                        /\ start_t[t2] >= sta[t1,t2] +  resampler_duration[resampl[t1,t2]] % Finishes before t2 starts
                        /\ resampler_duration[resampl[t1,t2]] = dur[t1,t2])
         /\ forall(t1, t2 in TASKS where resampl[t1,t2] = NoResampler)(dur[t1,t2] = 0)
         /\ duration_r = [dur[t1,t2] | t1, t2 in TASKS]
         /\ let {array[1..max_resamplers] of var opt TIME : temp = [sta[t1,t2] | t1, t2 in TASKS where resampl[t1,t2] != NoResampler];} in
                 array_opt_eq(start_r, temp);

%To know if we are on a resampling subpath or not     
% TODO: write a predicate
% Idea: a subpath that starts by a downsample and finish by an upsample with no resamplers inside

% Check that there are no resampler on the path %TODO: take care of trailing zeroes
predicate no_resamplers(array[TASKS] of var TASKS0 : path) = 
  forall(i in 1..nbTasks - 1)(resampler[path[i], path[i - 1]] = NoResampler);


/******************************
 ** Scheduling the tasks
 *****************************/
 
array[TASKS] of int : duration;
/*  Maximum possible duration: execution of all tasks + all resamplers.
The bound is not tight, as we should only have two resamplers per branches...
*/
int : time = sum(duration) + sum(t1, t2 in TASKS where audiograph[t1,t2])(max_duration); 
set of int : TIME = 0..time;
array[TASKS] of var TIME : start;

% Precedence relation
constraint forall(t1, t2 in TASKS where audiograph[t1,t2])(start[t1] + duration[t1] <= start[t2]);
constraint active_resamplers_start_duration(resampler, resampler_dur, resampler_start, duration, start); % For resamplers

% We are on one processor...
constraint disjunctive(start ++ resampler_start, duration ++ resampler_dur);

% Respect deadline
% TODO: express duration of tasks when they are on a resampled branch
var int : total_duration = sum(duration) + sum(t1,t2 in TASKS where resampler[t1,t2] != NoResampler)(resampler_duration[resampler[t1,t2]]);
constraint total_duration < deadline;


/******************************
 ** Quality
 *****************************/

% Quality
var int: graph_quality;