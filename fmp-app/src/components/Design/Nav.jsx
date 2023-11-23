import React from 'react';
import {
  MDBContainer,
  MDBNavbar,
  MDBNavbarBrand
} from 'mdb-react-ui-kit';

export default function Navbar() {
  return (
    <header className='fixed-top'>
      <MDBNavbar light bgColor='light'>
        <MDBContainer fluid>
          <MDBNavbarBrand href='#'>
            <img
              src='logo_se.png'
              height='30'
              alt=''
              loading='lazy'
            />
            Fm Playground
          </MDBNavbarBrand>
        </MDBContainer>
      </MDBNavbar>
    </header>
  );
}