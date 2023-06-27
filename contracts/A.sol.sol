contract A {uint256 old_z;
    uint z;
    /// ensures(true, z == 9)
    function a() public {(bool __v1, bool __v2)=(true, z == 9);
        b();
        z = 10;
    }
    /// ensures(true, z == 11)
    function b() public {(bool __v1, bool __v2)=(true, z == 11);
        c();
        z = 11;
    }
    /// ensures(true, z == 11)
    function c() public {(bool __v1, bool __v2)=(true, z == 11);
        z = 11;
    }
    /// ensures(true, z == 8)
    function d() public {(bool __v1, bool __v2)=(true, z == 8);
        c();
        z = 11;
    }
    /// ensures(true, z > 10)
    function zok() public {(bool __v1, bool __v2)=(true, z > 10);
        z = 9;
    }
}