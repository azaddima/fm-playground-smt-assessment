import React from "react";
import {
  MDBBtn,
  MDBModal,
  MDBModalDialog,
  MDBModalContent,
  MDBModalHeader,
  MDBModalTitle,
  MDBModalBody,
  MDBModalFooter,
} from "mdb-react-ui-kit";

/**
 * This component displays the Nuxmv CopyRight Notice.
 * According to the Nuxmv License, this notice must be displayed to the user.
 * @see {@link https://nuxmv.fbk.eu/downloads/LICENSE.txt} § 1
 * ... That you will not remove any Copyright or other notices from the Software.
 * We separate this notice from the output area to prettify the output.
 * User can still see the notice by clicking the "Nuxmv CopyRight Notice" button.
 * @param isNuxmvModalOpen - A boolean value that indicates whether the Nuxmv CopyRight Notice is open or not.
 * @param setIsNuxmvModalOpen - A function that sets the value of isNuxmvModalOpen.
 * @param toggleNuxmvModal - A function that toggles the value of isNuxmvModalOpen.
 * @returns A React Fragment that displays the Nuxmv CopyRight Notice.
 */
const NuxmvCopyrightNotice = ({
  isNuxmvModalOpen,
  setIsNuxmvModalOpen,
  toggleNuxmvModal,
}) => {
  return (
    <>
      <MDBModal
        open={isNuxmvModalOpen}
        setopen={setIsNuxmvModalOpen}
        tabIndex="-1"
      >
        <MDBModalDialog>
          <MDBModalContent>
            <MDBModalHeader>
              <MDBModalTitle>Nuxmv Copyright Notice</MDBModalTitle>
              <MDBBtn
                className="btn-close"
                color="none"
                onClick={toggleNuxmvModal}
              ></MDBBtn>
            </MDBModalHeader>
            <MDBModalBody style={{ maxHeight: "50vh", overflowY: "auto" }}>
              <p>
                *** This is nuXmv 2.0.0 (compiled on Mon Oct 14 18:05:39 2019){" "}
                <br /> *** Copyright (c) 2014-2019, Fondazione Bruno Kessler{" "}
                <br /> *** For more information on nuXmv see
                https://nuxmv.fbk.eu <br /> *** or email to
                &lt;nuxmv@list.fbk.eu&gt;. <br /> *** Please report bugs at
                https://nuxmv.fbk.eu/bugs <br /> *** (click on &quot;Login
                Anonymously&quot; to access) <br /> *** Alternatively write to
                &lt;nuxmv@list.fbk.eu&gt;. <br /> *** This version of nuXmv is
                linked to NuSMV 2.6.0. <br /> *** For more information on NuSMV
                see &lt;http://nusmv.fbk.eu&gt; <br /> *** or email to
                &lt;nusmv-users@list.fbk.eu&gt;. <br /> *** Copyright (C)
                2010-2019, Fondazione Bruno Kessler <br /> *** This version of
                nuXmv is linked to the CUDD library version 2.4.1 <br /> ***
                Copyright (c) 1995-2004, Regents of the University of Colorado{" "}
                <br /> *** This version of nuXmv is linked to the MiniSat SAT
                solver. <br /> *** See http://minisat.se/MiniSat.html <br /> ***
                Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson <br /> ***
                Copyright (c) 2007-2010, Niklas Sorensson <br /> *** This
                version of nuXmv is linked to MathSAT <br /> *** Copyright (C)
                2009-2019 by Fondazione Bruno Kessler <br /> *** Copyright (C)
                2009-2019 by University of Trento and others <br /> *** See
                http://mathsat.fbk.eu
              </p>
            </MDBModalBody>
            <MDBModalFooter>
              <MDBBtn color="secondary" onClick={toggleNuxmvModal}>
                Close
              </MDBBtn>
            </MDBModalFooter>
          </MDBModalContent>
        </MDBModalDialog>
      </MDBModal>
    </>
  );
};

export default NuxmvCopyrightNotice;
