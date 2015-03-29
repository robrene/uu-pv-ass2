#define N 10
#define SEED 12345

ltl processesAlwaysTerminate { []<>(activeProcesses == 0) }

mtype { xmsg_one, xmsg_two, leader_bcast };

int leaders[N];
int activeProcesses;

proctype P(chan in, out; int i, x)
{
  xr in;
  xs out;

  int leader_x = x;
  int xprime;

  printf("\nProcess %d with id %d", i, x);

  out ! xmsg_one(x);

  /* Round one: Pass larger IDs. Non-deterministic chance that other IDs get a wildcard pass. */
  do
  :: in ? xmsg_one(xprime) ->
    if
    :: (xprime < x) ->
      if
      :: printf("\nProcess %d (%d) discards x' %d", i, x, xprime); skip;
      :: printf("\nProcess %d (%d) grants x' %d a wildcard!", i, x, xprime); out ! xmsg_one(xprime);
      fi;
    :: (xprime > x) ->
      printf("\nProcess %d (%d) forwards x' %d", i, x, xprime);
      out ! xmsg_one(xprime);
    :: (xprime == x) ->
      printf("\nProcess %d (%d) enters round two, is nominated to become the leader!", i, x);
      leader_x = x;
      out ! xmsg_two(x);
      goto round_two;
    fi;
  :: in ? xmsg_two(xprime) ->
    printf("\nProcess %d (%d) enters round two, notes %d as possible leader.", i, x, xprime);
    leader_x = xprime;
    out ! xmsg_two(xprime);
    goto round_two;
  od

  /* Round two: Only nominated leader IDs get passed. Pass the lowest one. */
  round_two:
  do
  :: in ? xmsg_two(xprime) ->
    if
    :: (xprime > leader_x) ->
      printf("\nProcess %d (%d) discards nominated x' %d", i, x, xprime);
    :: (xprime < leader_x) ->
      printf("\nProcess %d (%d) forwards nominated x' %d", i, x, xprime);
      leader_x = xprime;
      out ! xmsg_two(xprime);
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
  :: (leader_x == x) -> printf("\nProcess %d (%d) LEADER", i, x);
  :: else -> printf ("\nProcess %d (%d) SLAVE", i, x);
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
