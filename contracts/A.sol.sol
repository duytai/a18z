contract A {uint256 old_z;
    uint z;
    /// ensures(true, z == 10 && 11 >= old(z))
    function a() public {(bool __v1, bool __v2)=(true, z == 10 && 11 >= old_z);
        b();
        z = 10;
    }
    /// ensures(true, z <= 11)
    function b() public {(bool __v1, bool __v2)=(true, z <= 11);
        c();
        z = 11;
    }
    /// ensures(true, z >= 11)
    function c() public {(bool __v1, bool __v2)=(true, z >= 11);
        z = 11;
    }
    /// ensures(true, z == 11 && old(z) >= 11)
    function d() public {(bool __v1, bool __v2)=(true, z == 11 && old_z >= 11);
        c();
        z = 11;
    }
    /// ensures(true, z == 9)
    function zok() public {(bool __v1, bool __v2)=(true, z == 9);
        z = 9;
    }
}