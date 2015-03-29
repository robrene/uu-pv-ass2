#define N 10
#define SEED 12345

ltl processesAlwaysTerminate { []<>(activeProcesses == 0) }

mtype { xmsg, leader_bcast };

int leaders[N];
int activeProcesses;

proctype P(chan in, out; int i, x)
{
  xr in;
  xs out;

  int leader_x;
  int xprime;

  printf("\nProcess %d with id %d", i, x);

  /* (1) Every process i sends its ID to its sucessor in the ring. */
  out ! xmsg(x);

  do
  /* (2) When a process i with ID x_i receives an id x' from its predecessor, ... */
  :: in ? xmsg(xprime) ->
    if
    /* (a) If x' < x_i, it discards x'. */
    :: (xprime < x) -> printf("\nProcess %d (%d) discards x' %d", i, x, xprime);
    /* (b) If x' > x_i, it forwards x' to its sucessor. */
    :: (xprime > x) ->
      printf("\nProcess %d (%d) forwards x' %d", i, x, xprime);
      out ! xmsg(xprime);
    /* (c) If x' = x_i the process wins and declares itself as the leader. */
    :: (xprime == x) ->
      printf("\nProcess %d (%d) has become the leader!", i, x);
      leader_x = x;
      out ! leader_bcast(leader_x);
    fi;
  :: in ? leader_bcast(xprime) ->
    printf("\nProcess %d (%d) has received leader broadcast of %d", i, x, xprime);
    if
    :: (xprime != x) ->
      leader_x = xprime;
      out ! leader_bcast(leader_x);
    :: else
      skip;
    fi;
    break;
  od

  if
  :: (leader_x == x) -> printf("\nProcess %d LEADER", i);
  :: else -> printf ("\nProcess %d SLAVE", i);
  fi;

  leaders[i] = leader_x;
  activeProcesses--;
}

init
{
  chan q[N] = [2*N] of { mtype, int };

  int id;
  id = SEED;

  activeProcesses = 0;
  int i;
  atomic {
    i = 0;
    do
    :: i < N ->
      id = (3697 * id + 12345) % (2 << 15);
      run P(q[i], q[(i+1)%N], i, id);
      activeProcesses++;
      i++;
    :: i >= N -> break;
    od
  }

  if
  :: (activeProcesses == 0) ->
    int leader;
    leader = leaders[0];
    i = 1;
    do
    :: i < N ->
      assert (leaders[i] == leader);
      i++;
    :: i >= N -> break;
    od
  fi
}
