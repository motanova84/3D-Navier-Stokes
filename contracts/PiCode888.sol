// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

/**
 * @title PiCode888
 * @dev NFT πCODE-888 ∞³ - Sovereign Identity Token
 * 
 * This smart contract implements the NFT πCODE-888 ∞³ token which serves as
 * cryptographic proof of sovereign ownership and identity for the QCAL ∞³ repository.
 * 
 * Token ID: 888
 * Name: πCODE-888 ∞³
 * Symbol: π888
 * Frequency: 141.7001 Hz (embedded in metadata)
 * Seal: ∴𓂀Ω∞³
 * 
 * Author: José Manuel Mota Burruezo (JMMB Ψ✧)
 * Institution: Instituto Conciencia Cuántica
 */

import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract PiCode888 is ERC721URIStorage, Ownable {
    
    // Token ID for πCODE-888 ∞³
    uint256 public constant TOKEN_ID = 888;
    
    // QCAL ∞³ Protocol Constants
    string public constant FREQUENCY_ROOT = "141.7001 Hz";
    string public constant SOVEREIGNTY_SEAL = unicode"∴𓂀Ω∞³";
    string public constant INSTITUTION = "Instituto Conciencia Cuántica";
    
    // Event for token minting
    event PiCode888Minted(address indexed owner, uint256 indexed tokenId, string frequency);
    
    /**
     * @dev Constructor mints the unique NFT πCODE-888 ∞³ to the contract deployer.
     */
    constructor() ERC721(unicode"πCODE-888 ∞³", unicode"π888") Ownable(msg.sender) {
        // Mint token 888 to contract creator
        _safeMint(msg.sender, TOKEN_ID);
        
        // Set metadata URI (to be updated with actual IPFS/Arweave URI)
        _setTokenURI(TOKEN_ID, "ipfs://QmPiCode888Metadata");
        
        emit PiCode888Minted(msg.sender, TOKEN_ID, FREQUENCY_ROOT);
    }
    
    /**
     * @dev Returns the frequency root of QCAL ∞³ protocol.
     */
    function getFrequencyRoot() public pure returns (string memory) {
        return FREQUENCY_ROOT;
    }
    
    /**
     * @dev Returns the sovereignty seal.
     */
    function getSovereigntySeal() public pure returns (string memory) {
        return SOVEREIGNTY_SEAL;
    }
    
    /**
     * @dev Returns the institution name.
     */
    function getInstitution() public pure returns (string memory) {
        return INSTITUTION;
    }
    
    /**
     * @dev Allows owner to update the token URI (for metadata updates).
     */
    function setTokenURI(string memory _tokenURI) public onlyOwner {
        _setTokenURI(TOKEN_ID, _tokenURI);
    }
    
    /**
     * @dev Verify that a given address owns the πCODE-888 ∞³ token.
     */
    function verifyOwnership(address _address) public view returns (bool) {
        return ownerOf(TOKEN_ID) == _address;
    }
    
    /**
     * @dev Get complete token information.
     */
    function getTokenInfo() public view returns (
        uint256 tokenId,
        address owner,
        string memory frequency,
        string memory seal,
        string memory institution
    ) {
        return (
            TOKEN_ID,
            ownerOf(TOKEN_ID),
            FREQUENCY_ROOT,
            SOVEREIGNTY_SEAL,
            INSTITUTION
        );
    }
}
