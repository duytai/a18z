contract A {
    uint z;
    /// ensures(true, z == 9)
    function a() public {
        b();
        z = 10;
    }
    /// ensures(true, z == 11)
    function b() public {
        c();
        z = 11;
    }
    /// ensures(true, z == 11)
    function c() public {
        z = 11;
    }
    /// ensures(true, z == 8)
    function d() public {
        c();
        z = 11;
    }
    /// ensures(true, z > 10)
    function zok() public {
        z = 9;
    }
}