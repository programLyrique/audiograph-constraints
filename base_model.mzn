int : nbTasks;
set of int : TASKS = 1..nbTasks;
set of int: TASKS0 = 0..nbTasks;
array[TASKS, TASKS] of bool : audiograph; /* Adjacency matrix; feel free to use another representation*/
int : deadline;
int : samplerate; /* This is the normal samplerate in the graph */



/* Resamplers */
enum RESAMPLER;
RESAMPLER: NoResampler;
array[RESAMPLER] of 0..100 : quality;%You can compute it with the arctan formula (or just give an arbitrary value). 
array[RESAMPLER] of int : resampler_factor;% +2 = x 2 and -2 = / 2
array[RESAMPLER] of int : resampler_duration;%wcet

array[TASKS,TASKS] of var RESAMPLER : resampler; /* If there is a resampler or not on the edge between two tasks */


/******************************
 ** Scheduling the tasks
 *****************************/
 
array[TASKS] of int : duration; /* Duration of a task in normal mode (not degraded) */
/*  Maximum possible duration: execution of all tasks + all resamplers.
The bound is not tight, as we should only have two resamplers per branches...
*/
int : time = sum(duration) + sum(t1, t2 in TASKS where audiograph[t1,t2])(max_duration); 
set of int : TIME = 0..time;
array[TASKS] of var TIME : start; /* Start time of the task. You have to decide it depending on the dependency graph and the durations*/
/* Note that for the whole duration of the execution, you should also add the durations of the inserted resamplers.
Two tasks cannot be executed at the same time (nor at the same time as a resampler) -> disjunctive global constraint */


/******************************
 ** Quality
 *****************************/

% Quality
var int: graph_quality;


/* First level: only one downsampled subpath per path between inputs and outputs (we call such a path a branch).
Subtleties: in case of a Y, you can have two downsamplers and one upsampler (if imputs are up on the Y) or one downsampler and two upsamplers (if the input is down on the Y). In that case, 
there is one resampled subpath per path.

You should aim at maximizing the quality while respecting the deadline. If the total duration of all the tasks without resamplers is less than the deadline, no need to insert resamplers!
*/