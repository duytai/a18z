// contract A {
//   mapping(address => uint) balances;
  
//   /// ensures(a >= b, c == a - b)
//   function subtract(uint256 a, uint256 b) returns(uint c) {
//     assert(a >= b);
//     return a - b;
//   }

//   /// ensures(true, balances[msg.sender]==old(balances[msg.sender])-_value && balances[_to]==old(balances[_to])+_value)
//   function transfer(address _to, uint256 _value) public returns(bool success) {
//     assert(_value >= 10);
//     if (_value > 0) {
//       balances[msg.sender] = subtract(balances[msg.sender], _value);
//       balances[_to] += _value;
//       return true;
//     } else {
//       return false;
//     }
//   }
// }


contract A {mapping(address => uint256) old_balances;address old_icoContractAddress;uint256 old_MAX_UINT;
  mapping(address => uint256) balances;
  address icoContractAddress;
  // mapping(address => bool) restrictedAddresses;
  uint MAX_UINT;

  /// ensures(true, true)
  function mintTokens(address _to, uint256 _amount) {(bool __v1, bool __v2)=(true,  true);require(_amount >= 0);require(MAX_UINT >= 0);         
    if (msg.sender != icoContractAddress) throw;            // Only ICO address can mint tokens        
    // if (restrictedAddresses[_to]) throw;                    // Throw if user wants to send to restricted address       
    // require(balances[_to] + _amount < MAX_UINT);
    // assert(balances[_to] + _amount < MAX_UINT);
    if (balances[_to] + _amount < balances[_to]) throw;     // Check for overflows
    // supply += _amount;
    assert(balances[_to] + _amount <= MAX_UINT);                                      // Update total supply
    balances[_to] +=  _amount;                               // Set minted coins to target
    // Mint(_to, _amount);                                     // Create Mint event       
    // Transfer(0x0, _to, _amount);                            // Create Transfer event from 0x
  }
}