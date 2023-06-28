contract A {uint256 old_z;mapping(address => uint256) old_balances;
    uint z;
    mapping(address => uint) balances;
    /// ensures(true, balances[msg.sender] == 100)
    function a() public {(bool __v1, bool __v2)=(true,  balances[msg.sender] == 100);
        z = 10;
        balances[msg.sender] = 100;
        b();
    }
    /// ensures(true, z == 11 && balances[msg.sender] == 100)
    function b() public {(bool __v1, bool __v2)=(true,  z == 11 && balances[msg.sender] == 100);
        z = 11;
        balances[msg.sender] += 100;
    }
}