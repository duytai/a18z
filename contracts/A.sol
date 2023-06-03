contract X {
  mapping(uint => uint) balances;
  mapping(uint => uint) old_balances;
  function sub(uint x, uint y) public pure returns(uint z) {
    (bool __v1, bool __v2) = (x >= 10, x >= 2);
    z = x + y;
    z = z - y;
  }

  function test(uint x) public {
    (bool __v1, bool __v2) = (true, balances[0] == old_balances[x] - 0);
    if (x > 0) {
      balances[x] = sub(balances[x], 0);
    } else {
      x = 20;
    }
  }
}
