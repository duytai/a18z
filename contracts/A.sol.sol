contract A {uint256 old_z;mapping(address => uint256) old_balances;
    uint z;
    mapping(address => uint) balances;
    /// ensures(true, z == 10)
    function a() public {(bool __v1, bool __v2)=(true,  z == 10&&old_z == old_z);
        z = 10;
        b();
        balances[address(0)] = 30;
    }

    /// ensures(true, z >= 20)
    function b() public {(bool __v1, bool __v2)=(true,  z >= 20&&old_z == old_z);
        z = 21;
    }

    function ok() public {(bool __v1, bool __v2)=(1==1, 1==0&&old_z == old_z);
        z = 40;
    }
}