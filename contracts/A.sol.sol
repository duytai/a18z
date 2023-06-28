contract A {uint256 old_z;mapping(address => uint256) old_balances;
    uint z;
    mapping(address => uint) balances;
    /// ensures(true, z == 9)
    function a() public {(bool __v1, bool __v2)=(true,  z == 9);
        z = 10;
        b();
        balances[msg.sender] = 100;
    }
    /// ensures(true, z == 11)
    function b() public {(bool __v1, bool __v2)=(true,  z == 11);
        z = 11;
    }
}