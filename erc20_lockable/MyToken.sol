pragma solidity 0.4.24;

contract Ownable {
    address public owner;

    constructor() public {
        owner = msg.sender;
    }

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function owner() view external returns (address){
        return owner;
    }
	 
    function transferOwnership(address _newOwner) external onlyOwner {
        require(_newOwner != address(0));
        emit OwnershipTransferred(owner, _newOwner);
        owner = _newOwner;
    }

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);
}

contract UnLock {
    uint256 public UnLockTime;

    modifier isUnLocked() {
        require(block.timestamp > UnLockTime);
        _;
    }
}

contract ERC20Token is UnLock {
    
    uint256 constant MAX_UINT256 = 2**256 - 1;

    string public name;                                  
    string public symbol;
    uint8 public decimals; 

    uint256 public totalSupply;
    mapping (address => uint256) public balances;
    mapping (address => mapping (address => uint256)) public allowed;

    function name() public view returns (string){
        return name;
    }

    function symbol() public view returns (string){
        return symbol;
    }

    function decimals() public view returns (uint8){
        return decimals;
    }

    function totalSupply() public view returns (uint256){
        return totalSupply;
    }

    function balanceOf(address _owner) public view returns (uint256){
        return balances[_owner];
    }

    function transfer(address _to, uint256 _value) isUnLocked public returns (bool success){
        require (balances[_to] + _value >= balances[_to]);
        require (balances[msg.sender] >= _value);
        balances[_to] = balances[_to] + _value;
        balances[msg.sender] = balances[_to] + _value;
        emit Transfer(msg.sender, _to, _value);
        return true;
    }

    function transferFrom(address _from, address _to, uint256 _value) isUnLocked public returns (bool success){
        uint256 allowance = allowed[_from][msg.sender];
        require (balances[_to] + _value >= balances[_to]);
        require (balances[_from] >= _value);
        require (allowance >= _value);
        balances[_to] = balances[_to] + _value;
        balances[_from] = balances[_from] - _value;
       
        if (allowance < MAX_UINT256) {
            allowed[_from][msg.sender] = allowed[_from][msg.sender] - _value;
        }
        emit Transfer(_from, _to, _value);
        return true;
    }

    function approve(address _spender, uint256 _value) isUnLocked public returns (bool){
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);
        return true;
    }

    function allowance(address _owner, address _spender) public view returns (uint256){
        return allowed[_owner][_spender];
    }

    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    event Approval(address indexed _owner, address indexed _spender, uint256 _value);
}

contract MyToken is ERC20Token {
    
    constructor(uint256 _initialAmount, string _name, string _symbol, uint8 _decimals, uint256 _unLockTime) public {

        require (_unLockTime >= block.timestamp);
        totalSupply = _initialAmount;
        balances[msg.sender] = _initialAmount;
        name = _name;
        symbol = _symbol;
        decimals = _decimals;
        UnLockTime = _unLockTime;
        emit Transfer(0x0, msg.sender, _initialAmount);
    }

    function increaseApproval(address _spender, uint _addedValue) isUnLocked public returns (bool) {
        
        require (allowed[msg.sender][_spender]+ _addedValue >= allowed[msg.sender][_spender]);
        allowed[msg.sender][_spender] = allowed[msg.sender][_spender]+ _addedValue;
        emit Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
        return true;
    }

    function decreaseApproval(address _spender, uint _subtractedValue) isUnLocked public returns (bool success) {
        
        uint oldValue = allowed[msg.sender][_spender];
        if (_subtractedValue > oldValue) {
            allowed[msg.sender][_spender] = 0;
        } else {
            allowed[msg.sender][_spender] = oldValue - _subtractedValue;
        }
        emit Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
        return true;
    }
}