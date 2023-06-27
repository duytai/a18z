contract A {
    uint z;
    /// ensures(true, r == x)
    function add(uint x, uint y) pure public returns(uint r) {
        r = x + y;
    }

    /// ensures(true, z >= 30)
    function main(uint x, uint y) public {
        z = add(x, y);
        z = z - 20;
    }
}
// contract A {
//     uint z;
//     /// ensures(true, z == 9)
//     function a() public {
//         b();
//         z = 10;
//     }
//     /// ensures(true, z == 11)
//     function b() public {
//         c();
//         z = 11;
//     }
//     /// ensures(true, z >= 12)
//     function c() public {
//         z = 1;
//     }
//     /// ensures(true, z == 8)
//     function d() public {
//         c();
//         z = 11;
//     }
//     /// ensures(true, z > 10)
//     function zok() public {
//         z = 9;
//     }
// }