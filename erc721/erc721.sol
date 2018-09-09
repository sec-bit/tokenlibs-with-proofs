pragma solidity ^0.4.24;

contract ERC721Receiver {
    function onERC721Received(address _operator, address _from, uint256 _token, bytes _data)
        public returns(bytes4);
}

contract ERC721 {
    mapping(uint256 => address) public tokenOwner;
    mapping(uint256 => address) public tokenApprovals;
    mapping(address => uint256) public ownedTokensCount;
    mapping(address => mapping (address => bool)) public operatorApprovals;

    uint256 private constant max_uint256 = 2 ** 256 - 1;
    bytes4 private constant erc165_interface_id = 0x01ffc9a7;
    bytes4 private constant erc721_interface_id = 0x80ac58cd;
    bytes4 private constant ERC721_RECEIVED = 0x150b7a02;

    event Transfer(address indexed _from, address indexed _to, uint256 indexed _tokenId);
    event Approval(address indexed _owner, address indexed _approved, uint256 indexed _tokenId);
    event ApprovalForAll(address indexed _owner, address indexed _operator, bool _approved);

    constructor()
        public
    {
    }

    function balanceOf(address _owner)
        public view returns (uint256)
    {
        require(_owner != 0);
        return ownedTokensCount[_owner];
    }

    function ownerOf(uint256 _token)
        public view returns (address)
    {
        require(tokenOwner[_token] != 0);
        address owner = tokenOwner[_token];
        return owner;
    }

    function safeTransferFrom(address _from, address _to, uint256 _token, bytes _data)
        public
    {
        require(_to != 0);

        address owner = tokenOwner[_token];
        require((owner != 0) && (owner == _from));

        address sender = msg.sender;
        require((sender == owner) || (sender == tokenApprovals[_token]) || operatorApprovals[owner][sender]);

        tokenApprovals[_token] = 0;
        tokenOwner[_token] = _to;

        if (_from != _to) {
            require(ownedTokensCount[_to] <= max_uint256 - 1);
            ownedTokensCount[_from] -= 1;
            ownedTokensCount[_to] += 1;
        }

        emit Transfer(_from, _to, _token);

        if (isContract(_to)) {
            require(ERC721Receiver(_to).onERC721Received(_from, _to, _token, _data) == ERC721_RECEIVED);
        }
    }

    function safeTransferFrom(address _from, address _to, uint256 _token)
        public
    {
        require(_to != 0);

        address owner = tokenOwner[_token];
        require((owner != 0) && (owner == _from));

        address sender = msg.sender;
        require((sender == owner) || (sender == tokenApprovals[_token]) || operatorApprovals[owner][sender]);

        tokenApprovals[_token] = 0;
        tokenOwner[_token] = _to;

        if (_from != _to) {
            require(ownedTokensCount[_to] <= max_uint256 - 1);
            ownedTokensCount[_from] -= 1;
            ownedTokensCount[_to] += 1;
        }

        emit Transfer(_from, _to, _token);

        if (isContract(_to)) {
            require(ERC721Receiver(_to).onERC721Received(_from, _to, _token, "") == ERC721_RECEIVED);
        }
    }

    function transferFrom(address _from, address _to, uint256 _token)
        public
    {
        require(_to != 0);

        address owner = tokenOwner[_token];
        require((owner != 0) && (owner == _from));

        address sender = msg.sender;
        require((sender == owner) || (sender == tokenApprovals[_token]) || operatorApprovals[owner][sender]);

        tokenApprovals[_token] = 0;
        tokenOwner[_token] = _to;
        if (_from != _to) {
            require(ownedTokensCount[_to] <= max_uint256 - 1);
            ownedTokensCount[_from] -= 1;
            ownedTokensCount[_to] += 1;
        }

        emit Transfer(_from, _to, _token);
    }

    function approve(address _approved, uint256 _token)
        public
    {
        address owner = tokenOwner[_token];
        require(_approved != owner);

        address sender = msg.sender;
        require((sender == owner) || operatorApprovals[owner][sender]);

        tokenApprovals[_token] = _approved;
        emit Approval(owner, _approved, _token);
    }

    function setApprovalForAll(address _operator, bool _approved)
        public
    {
        address sender = msg.sender;
        require(_operator != sender);

        operatorApprovals[sender][_operator] = _approved;
        emit ApprovalForAll(sender, _operator, _approved);
    }

    function getApproved(uint256 _token)
        public view returns (address)
    {
        require(tokenOwner[_token] != 0);
        return tokenApprovals[_token];
    }

    function isApprovedForAll(address _owner, address _operator)
        public view returns (bool)
    {
        return operatorApprovals[_owner][_operator];
    }

    function supportedInterface(bytes4 _id)
        public pure returns (bool)
    {
        if (_id == erc165_interface_id) {
            return true;
        } else if (_id == erc721_interface_id) {
            return true;
       } else {
            return false;
       }
    }

    function isContract(address _account)
        internal view returns (bool)
    {
        uint256 size;
        assembly { size := extcodesize(_account) }
        return size > 0;
    }
}
