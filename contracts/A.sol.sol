contract X {mapping(uint256 => uint256) old_balances;uint256 old_z;
  mapping(uint => uint) balances;
  uint z;
  /// ensures(x >= y, r == x - y && z == old(z) + 20)
  function sub(uint x, uint y) private returns(uint r) {(bool __v1, bool __v2)=(x >= y, r == x - y && z == old_z + 20);
    r = x - y;
    z = z + 20;
  }

  /// ensures(z >= 10, z == old(z) + 20)
  function test() public {(bool __v1, bool __v2)=(z >= 10, z == old_z + 20);
    sub(30, 10);
  }
}
