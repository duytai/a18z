/**
 *Submitted for verification at Etherscan.io on 2017-05-29
*/

pragma solidity ^0.4.10;

/* taking ideas from FirstBlood token */
contract SafeMath {

    /* function assert(bool assertion) internal { */
    /*   if (!assertion) { */
    /*     throw; */
    /*   } */
    /* }      // assert no longer needed once solidity is on 0.4.10 */
    /// ensures(true, r == x + y)
    function safeAdd(uint256 x, uint256 y) internal returns(uint256 r) {
      uint256 z = x + y;
      assert((z >= x) && (z >= y));
      return z;
    }
    /// ensures(x >= y, r == x -y)
    function safeSubtract(uint256 x, uint256 y) internal returns(uint256 r) {
      assert(x >= y);
      uint256 z = x - y;
      return z;
    }
    /// ensures(true, r == x * y)
    function safeMult(uint256 x, uint256 y) internal returns(uint256 r) {
      uint256 z = x * y;
      // assert((x == 0)||(z/x == y));
      return z;
    }

}

contract Token {
    uint256 public totalSupply;
    function balanceOf(address _owner) constant returns (uint256 balance);
    function transfer(address _to, uint256 _value) returns (bool success);
    function transferFrom(address _from, address _to, uint256 _value) returns (bool success);
    function approve(address _spender, uint256 _value) returns (bool success);
    function allowance(address _owner, address _spender) constant returns (uint256 remaining);
    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    event Approval(address indexed _owner, address indexed _spender, uint256 _value);
}


/*  ERC 20 token */
contract StandardToken is Token {
    /// ensures(balances[msg.sender] >= _value && msg.sender != _to, balances[msg.sender] == old(balances[msg.sender]) - _value && balances[_to] == old(balances[_to]) + _value)
    function transfer(address _to, uint256 _value) returns (bool success) {
      if (balances[msg.sender] >= _value && _value > 0) {
        balances[msg.sender] -= _value;
        balances[_to] += _value;
        Transfer(msg.sender, _to, _value);
        return true;
      } else {
        return false;
      }
    }
    /// ensures(balances[_from] >= _value && _to != _from && allowed[_from][msg.sender] >= _value && _value > 0, balances[_to] == old(balances[_to]) + _value && balances[_from] == old(balances[_from]) - _value && allowed[_from][msg.sender] == old(allowed[_from][msg.sender]) - _value)
    function transferFrom(address _from, address _to, uint256 _value) returns (bool success) {
      if (balances[_from] >= _value && allowed[_from][msg.sender] >= _value && _value > 0) {
        balances[_to] += _value;
        balances[_from] -= _value;
        allowed[_from][msg.sender] -= _value;
        Transfer(_from, _to, _value);
        return true;
      } else {
        return false;
      }
    }
    /// ensures(true, balance == balances[_owner])
    function balanceOf(address _owner) constant returns (uint256 balance) {
        return balances[_owner];
    }
    /// ensures(true, allowed[msg.sender][_spender] == _value)
    function approve(address _spender, uint256 _value) returns (bool success) {
        allowed[msg.sender][_spender] = _value;
        Approval(msg.sender, _spender, _value);
        return true;
    }
    /// ensures(true, remaining == allowed[_owner][_spender])
    function allowance(address _owner, address _spender) constant returns (uint256 remaining) {
      return allowed[_owner][_spender];
    }

    mapping (address => uint256) balances;
    mapping (address => mapping (address => uint256)) allowed;
}

contract BAToken is StandardToken, SafeMath {

    // metadata
    string public constant name = "Basic Attention Token";
    string public constant symbol = "BAT";
    uint256 public constant decimals = 18;
    string public version = "1.0";

    // contracts
    address public ethFundDeposit;      // deposit address for ETH for Brave International
    address public batFundDeposit;      // deposit address for Brave International use and BAT User Fund

    // crowdsale parameters
    bool public isFinalized;              // switched to true in operational state
    uint256 public fundingStartBlock;
    uint256 public fundingEndBlock;
    uint256 public constant batFund = 500 * (10**6) * 10**decimals;   // 500m BAT reserved for Brave Intl use
    uint256 public constant tokenExchangeRate = 6400; // 6400 BAT tokens per 1 ETH
    uint256 public constant tokenCreationCap =  1500 * (10**6) * 10**decimals;
    uint256 public constant tokenCreationMin =  675 * (10**6) * 10**decimals;


    // events
    event LogRefund(address indexed _to, uint256 _value);
    event CreateBAT(address indexed _to, uint256 _value);

    /// ensures(true, !isFinalized && ethFundDeposit == _ethFundDeposit && batFundDeposit == _batFundDeposit && fundingStartBlock == _fundingStartBlock && fundingEndBlock == _fundingEndBlock && totalSupply == batFund && balances[batFundDeposit] == batFund)
    function BAToken(
        address _ethFundDeposit,
        address _batFundDeposit,
        uint256 _fundingStartBlock,
        uint256 _fundingEndBlock)
    {
      isFinalized = false;                   //controls pre through crowdsale state
      ethFundDeposit = _ethFundDeposit;
      batFundDeposit = _batFundDeposit;
      fundingStartBlock = _fundingStartBlock;
      fundingEndBlock = _fundingEndBlock;
      totalSupply = batFund;
      balances[batFundDeposit] = batFund;    // Deposit Brave Intl share
      CreateBAT(batFundDeposit, batFund);  // logs Brave Intl fund
    }
    /// ensures(!isFinalized && block.number >= fundingStartBlock && block.number <= fundingEndBlock && msg.value > 0 && tokenExchangeRate >= 0 && totalSupply >= 0 && msg.value * tokenExchangeRate + totalSupply <= tokenCreationCap, totalSupply == old(totalSupply) + msg.value * tokenExchangeRate && balances[msg.sender] == old(balances[msg.sender]) + msg.value * tokenExchangeRate)
    function createTokens() payable external {
      if (isFinalized) throw;
      if (block.number < fundingStartBlock) throw;
      if (block.number > fundingEndBlock) throw;
      if (msg.value == 0) throw;

      uint256 tokens = safeMult(msg.value, tokenExchangeRate); // check that we're not over totals
      uint256 checkedSupply = safeAdd(totalSupply, tokens);

      // return money if something goes wrong
      if (tokenCreationCap < checkedSupply) throw;  // odd fractions won't be found

      totalSupply = checkedSupply;
      balances[msg.sender] += tokens;  // safeAdd not needed; bad semantics to use here
      CreateBAT(msg.sender, tokens);  // logs token creation
    }

    /// ensures(!isFinalized && msg.sender == ethFundDeposit && totalSupply >= tokenCreationMin && (block.number > fundingEndBlock || totalSupply == tokenCreationCap), isFinalized)
    function finalize() external {
      if (isFinalized) throw;
      if (msg.sender != ethFundDeposit) throw; // locks finalize to the ultimate ETH owner
      if(totalSupply < tokenCreationMin) throw;      // have to sell minimum to move to operational
      if(block.number <= fundingEndBlock && totalSupply != tokenCreationCap) throw;
      // move to operational
      isFinalized = true;
      //if(!ethFundDeposit.send(this.balance)) throw;  // send the eth to Brave International
    }

     /// ensures(!isFinalized && block.number > fundingEndBlock && totalSupply < tokenCreationMin && msg.sender != batFundDeposit && balances[msg.sender] > 0 && totalSupply > balances[msg.sender], totalSupply == old(totalSupply) - old(balances[msg.sender]) && balances[msg.sender] == 0)
    function refund() external {
      if(isFinalized) throw;                       // prevents refund if operational
      if (block.number <= fundingEndBlock) throw; // prevents refund until sale period is over
      if(totalSupply >= tokenCreationMin) throw;  // no refunds if we sold enough
      if(msg.sender == batFundDeposit) throw;    // Brave Intl not entitled to a refund
      uint256 batVal = balances[msg.sender];
      if (batVal == 0) throw;
      balances[msg.sender] = 0;
      totalSupply = safeSubtract(totalSupply, batVal); // extra safe
      uint256 ethVal = batVal / tokenExchangeRate;     // should be safe; previous throws covers edges
      LogRefund(msg.sender, ethVal);               // log it 
      // if (!msg.sender.send(ethVal)) throw;       // if you're using a contract; make sure it works with .send gas limits
    }

}