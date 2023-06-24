/**
 *Submitted for verification at Etherscan.io on 2018-02-01
*/

// pragma solidity ^0.4.18;


/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {address old_owner;
  address public owner;


  event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);


  /**
   * @dev The Ownable constructor sets the original `owner` of the contract to the sender
   * account.
   */
  /// ensures(true, owner == msg.sender)
  function Ownable() public {(bool __v1, bool __v2)=(true, owner == msg.sender);
    owner = msg.sender;
  }


  /**
   * @dev Throws if called by any account other than the owner.
   */
  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }


  /**
   * @dev Allows the current owner to transfer control of the contract to a newOwner.
   * @param newOwner The address to transfer ownership to.
   */
  /// ensures(msg.sender == owner && newOwner != address(0), owner == newOwner)
  function transferOwnership(address newOwner) public onlyOwner {(bool __v1, bool __v2)=(msg.sender == owner && newOwner != address(0), owner == newOwner);
    require(newOwner != address(0));
    OwnershipTransferred(owner, newOwner);
    owner = newOwner;
  }

}
/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {
  /// ensures(true, r == a * b)
  function mul(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(true, r == a * b);require(a >= 0);require(b >= 0);
    if (a == 0) {
      return 0;
    }
    uint256 c = a * b;
    // assert(c / a == b);
    return c;
  }
  /// ensures(true, r == a / b)
  function div(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(true, r == a / b);require(a >= 0);require(b >= 0);
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return c;
  }
  /// ensures(a >= b, r == a - b)
  function sub(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(a >= b, r == a - b);require(a >= 0);require(b >= 0);
    assert(b <= a);
    return a - b;
  }
  /// ensures(true, r == a + b)
  function add(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(true, r == a + b);require(a >= 0);require(b >= 0);
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}

// This is an ERC-20 token contract based on Open Zepplin's StandardToken
// and MintableToken plus the ability to burn tokens.
//
// We had to copy over the code instead of inheriting because of changes
// to the modifier lists of some functions:
//   * transfer(), transferFrom() and approve() are not callable during
//     the minting period, only after MintingFinished()
//   * mint() can only be called by the minter who is not the owner
//     but the HoloTokenSale contract.
//
// Token can be burned by a special 'destroyer' role that can only
// burn its tokens.
contract HoloToken is Ownable {string old_name;string old_symbol;uint8 old_decimals;uint256 old_totalSupply;mapping(address => uint256) old_balances;mapping(address => mapping(address => uint256)) old_allowed;bool old_mintingFinished;address old_destroyer;address old_minter;
  string public constant name = "HoloToken";
  string public constant symbol = "HOT";
  uint8 public constant decimals = 18;

  event Transfer(address indexed from, address indexed to, uint256 value);
  event Approval(address indexed owner, address indexed spender, uint256 value);
  event Mint(address indexed to, uint256 amount);
  event MintingFinished();
  event Burn(uint256 amount);

  uint256 public totalSupply;


  //==================================================================================
  // Zeppelin BasicToken (plus modifier to not allow transfers during minting period):
  //==================================================================================

  using SafeMath for uint256;

  mapping(address => uint256) public balances;

  /**
  * @dev transfer token for a specified address
  * @param _to The address to transfer to.
  * @param _value The amount to be transferred.
  */
  /// ensures(msg.sender != _to && mintingFinished && _to != address(0) && _value <= balances[msg.sender], balances[msg.sender] == old(balances[msg.sender]) - _value && balances[_to] == old(balances[_to]) + _value)
  function transfer(address _to, uint256 _value) public whenMintingFinished returns (bool) {(bool __v1, bool __v2)=(msg.sender != _to && mintingFinished && _to != address(0) && _value <= balances[msg.sender], balances[msg.sender] == old_balances[msg.sender] - _value && balances[_to] == old_balances[_to] + _value);require(_value >= 0);
    require(_to != address(0));
    require(_value <= balances[msg.sender]);

    // SafeMath.sub will throw if there is not enough balance.
    balances[msg.sender] = balances[msg.sender].sub(_value);
    balances[_to] = balances[_to].add(_value);
    Transfer(msg.sender, _to, _value);
    return true;
  }

  /**
  * @dev Gets the balance of the specified address.
  * @param _owner The address to query the the balance of.
  * @return An uint256 representing the amount owned by the passed address.
  */
  /// ensures(true, balance == balances[_owner])
  function balanceOf(address _owner) public view returns (uint256 balance) {(bool __v1, bool __v2)=(true, balance == balances[_owner]);
    return balances[_owner];
  }


  //=====================================================================================
  // Zeppelin StandardToken (plus modifier to not allow transfers during minting period):
  //=====================================================================================
  mapping (address => mapping (address => uint256)) public allowed;


  /**
   * @dev Transfer tokens from one address to another
   * @param _from address The address which you want to send tokens from
   * @param _to address The address which you want to transfer to
   * @param _value uint256 the amout of tokens to be transfered
   */
  /// ensures(_from != _to && mintingFinished && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender], balances[_from] == old(balances[_from]) - _value && balances[_to] == old(balances[_to]) + _value)
  function transferFrom(address _from, address _to, uint256 _value) public whenMintingFinished returns (bool) {(bool __v1, bool __v2)=(_from != _to && mintingFinished && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender], balances[_from] == old_balances[_from] - _value && balances[_to] == old_balances[_to] + _value);require(_value >= 0);
    require(_to != address(0));
    require(_value <= balances[_from]);
    require(_value <= allowed[_from][msg.sender]);

    balances[_from] = balances[_from].sub(_value);
    balances[_to] = balances[_to].add(_value);
    allowed[_from][msg.sender] = allowed[_from][msg.sender].sub(_value);
    Transfer(_from, _to, _value);
    return true;
  }

  /**
   * @dev Approve the passed address to spend the specified amount of tokens on behalf of msg.sender.
   *
   * Beware that changing an allowance with this method brings the risk that someone may use both the old
   * and the new allowance by unfortunate transaction ordering. One possible solution to mitigate this
   * race condition is to first reduce the spender's allowance to 0 and set the desired value afterwards:
   * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
   * @param _spender The address which will spend the funds.
   * @param _value The amount of tokens to be spent.
   */
  /// ensures(mintingFinished, allowed[msg.sender][_spender] == _value)
  function approve(address _spender, uint256 _value) public whenMintingFinished returns (bool) {(bool __v1, bool __v2)=(mintingFinished, allowed[msg.sender][_spender] == _value);require(_value >= 0);
    allowed[msg.sender][_spender] = _value;
    Approval(msg.sender, _spender, _value);
    return true;
  }

  /**
   * @dev Function to check the amount of tokens that an owner allowed to a spender.
   * @param _owner address The address which owns the funds.
   * @param _spender address The address which will spend the funds.
   * @return A uint256 specifying the amount of tokens still available for the spender.
   */
   /// ensures(true, r == allowed[_owner][_spender])
  function allowance(address _owner, address _spender) public view returns (uint256 r) {(bool __v1, bool __v2)=(true, r == allowed[_owner][_spender]);
    return allowed[_owner][_spender];
  }

  /**
   * approve should be called when allowed[_spender] == 0. To increment
   * allowed value is better to use this function to avoid 2 calls (and wait until
   * the first transaction is mined)
   * From MonolithDAO Token.sol
   */
  /// ensures(true, allowed[msg.sender][_spender] == old(allowed[msg.sender][_spender]) + _addedValue)
  function increaseApproval(address _spender, uint _addedValue) public returns (bool) {(bool __v1, bool __v2)=(true, allowed[msg.sender][_spender] == old_allowed[msg.sender][_spender] + _addedValue);require(_addedValue >= 0);
    allowed[msg.sender][_spender] = allowed[msg.sender][_spender].add(_addedValue);
    Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    return true;
  }

  /// ensures(_subtractedValue <= allowed[msg.sender][_spender], allowed[msg.sender][_spender] == old(allowed[msg.sender][_spender]) - _subtractedValue)
  function decreaseApproval(address _spender, uint _subtractedValue) public returns (bool) {(bool __v1, bool __v2)=(_subtractedValue <= allowed[msg.sender][_spender], allowed[msg.sender][_spender] == old_allowed[msg.sender][_spender] - _subtractedValue);require(_subtractedValue >= 0);
    uint oldValue = allowed[msg.sender][_spender];
    if (_subtractedValue > oldValue) {
      allowed[msg.sender][_spender] = 0;
    } else {
      allowed[msg.sender][_spender] = oldValue.sub(_subtractedValue);
    }
    Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    return true;
  }


  //=====================================================================================
  // Minting:
  //=====================================================================================

  bool public mintingFinished = false;
  address public destroyer;
  address public minter;

  modifier canMint() {
    require(!mintingFinished);
    _;
  }

  modifier whenMintingFinished() {
    require(mintingFinished);
    _;
  }

  modifier onlyMinter() {
    require(msg.sender == minter);
    _;
  }
  /// ensures(msg.sender == owner, minter == _minter)
  function setMinter(address _minter) external onlyOwner {(bool __v1, bool __v2)=(msg.sender == owner, minter == _minter);
    minter = _minter;
  }
  /// ensures(msg.sender == owner && !mintingFinished && balances[_to] + _amount > balances[_to] && totalSupply + _amount > totalSupply, totalSupply == old(totalSupply) + _amount && balances[_to] == old(balances[_to]) + _amount)
  function mint(address _to, uint256 _amount) external onlyMinter canMint  returns (bool) {(bool __v1, bool __v2)=(msg.sender == owner && !mintingFinished && balances[_to] + _amount > balances[_to] && totalSupply + _amount > totalSupply, totalSupply == old_totalSupply + _amount && balances[_to] == old_balances[_to] + _amount);require(_amount >= 0);require(totalSupply >= 0);
    require(balances[_to] + _amount > balances[_to]); // Guard against overflow
    require(totalSupply + _amount > totalSupply);     // Guard against overflow  (this should never happen)
    totalSupply = totalSupply.add(_amount);
    balances[_to] = balances[_to].add(_amount);
    Mint(_to, _amount);
    return true;
  }
  /// ensures(msg.sender == minter, mintingFinished)
  function finishMinting() external onlyMinter returns (bool) {(bool __v1, bool __v2)=(msg.sender == minter, mintingFinished);
    mintingFinished = true;
    MintingFinished();
    return true;
  }


  //=====================================================================================
  // Burning:
  //=====================================================================================


  modifier onlyDestroyer() {
     require(msg.sender == destroyer);
     _;
  }
  /// ensures(msg.sender == owner, destroyer == _destroyer)
  function setDestroyer(address _destroyer) external onlyOwner {(bool __v1, bool __v2)=(msg.sender == owner, destroyer == _destroyer);
    destroyer = _destroyer;
  }
  /// ensures(msg.sender == destroyer && balances[destroyer] >= _amount && _amount > 0 && totalSupply >= _amount, balances[destroyer] == old(balances[destroyer]) - _amount && totalSupply == old(totalSupply) - _amount)
  function burn(uint256 _amount) external onlyDestroyer {(bool __v1, bool __v2)=(msg.sender == destroyer && balances[destroyer] >= _amount && _amount > 0 && totalSupply >= _amount, balances[destroyer] == old_balances[destroyer] - _amount && totalSupply == old_totalSupply - _amount);require(_amount >= 0);require(totalSupply >= 0);
    require(balances[destroyer] >= _amount && _amount > 0);
    balances[destroyer] = balances[destroyer].sub(_amount);
    totalSupply = totalSupply.sub(_amount);
    Burn(_amount);
  }
}